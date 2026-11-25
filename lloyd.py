#!/usr/bin/env python3

# SPDX-License-Identifier: BSD-3-Clause
# Copyright (c) 2026 97neko75

"""Lloyd reference checker: deterministic intuitionistic propositional fragment.

This single-file program implements a deliberately small, explicit fragment of
LRS-Alpha. It checks propositional proofs with a Curry-Howard natural-deduction
kernel. It does not implement the dependent-type kernel described in LRS-Alpha.

Supported source declarations include both the long form and the compact form:
    Axiom NAME: FORMULA.
    Theorem NAME.
      Claim: FORMULA.
      Proof.
        Step NAME: FORMULA, by [PROOF_TERM].
        Hence FORMULA by [PROOF_TERM].
      QED.

    Axiom NAME : FORMULA
    Theorem NAME : FORMULA
    Proof
      PROOF_TERM
    .
    Print axioms NAME

Formula syntax:
    atom | True | False | not FORMULA | (FORMULA)
    FORMULA and FORMULA | FORMULA or FORMULA
    FORMULA /\\ FORMULA | FORMULA \\/ FORMULA
    FORMULA -> FORMULA | FORMULA <-> FORMULA

Proof terms are explicit calls; no unification or proof search is performed:
    NAME
    intro h : FORMULA => PROOF_TERM
    AndIntro PROOF_TERM PROOF_TERM
    h.1 | h.2
    imp_intro("h", formula("P"), PROOF)
    imp_apply(PROOF, PROOF)
    and_intro(PROOF, PROOF) | and_left(PROOF) | and_right(PROOF)
    or_left(PROOF, formula("Q")) | or_right(formula("P"), PROOF)
    or_cases(PROOF, "left_name", PROOF, "right_name", PROOF)
    false_elim(PROOF, formula("P"))
    iff_intro(PROOF, PROOF) | iff_left(PROOF) | iff_right(PROOF)

The input syntax is UTF-8. Each declaration or proof sentence occupies one line.
Names are case-sensitive. Formula atoms are identifiers; arithmetic expressions,
quantifiers, equality, induction, definitions, imports, recursion, certificates,
Lean interoperability, and dependent types are intentionally unsupported.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


class LloydError(Exception):
    """A source or kernel error with an optional source location."""

    def __init__(self, message: str, line: int | None = None):
        self.message = message
        self.line = line
        super().__init__(f"line {line}: {message}" if line is not None else message)


# ---------- Formula syntax ----------

@dataclass(frozen=True)
class Formula:
    tag: str
    name: str = ""
    left: Formula | None = None
    right: Formula | None = None

    def __str__(self) -> str:
        if self.tag == "atom":
            return self.name
        if self.tag == "true":
            return "True"
        if self.tag == "false":
            return "False"
        if self.tag == "not":
            assert self.left is not None
            inner = str(self.left)
            return f"not ({inner})" if self.left.tag in {"imp", "iff", "or"} else f"not {inner}"
        assert self.left is not None and self.right is not None
        if self.tag == "imp" and self.right.tag == "false":
            inner = str(self.left)
            return f"not ({inner})" if self.left.tag in {"imp", "iff", "or"} else f"not {inner}"
        op = {"and": "and", "or": "or", "imp": "->", "iff": "<->"}[self.tag]
        return f"({self.left} {op} {self.right})"


FormulaToken = re.compile(r"<->|->|/\\|\\/|[()]|[A-Za-z_][A-Za-z0-9_.]*")


class FormulaParser:
    PRECEDENCE = {"<->": 10, "->": 20, "or": 30, "\\/": 30, "and": 40, "/\\": 40}

    def __init__(self, source: str):
        self.source = source.strip()
        self.tokens = self._tokenize(self.source)
        self.pos = 0

    @staticmethod
    def _tokenize(source: str) -> list[str]:
        tokens: list[str] = []
        pos = 0
        while pos < len(source):
            if source[pos].isspace():
                pos += 1
                continue
            match = FormulaToken.match(source, pos)
            if not match:
                raise LloydError(f"unsupported formula character {source[pos]!r}")
            tokens.append(match.group(0))
            pos = match.end()
        return tokens

    def parse(self) -> Formula:
        if not self.tokens:
            raise LloydError("expected a formula")
        result = self._expr(0)
        if self.pos != len(self.tokens):
            raise LloydError(f"unexpected formula token {self.tokens[self.pos]!r}")
        return result

    def _peek(self) -> str | None:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def _expr(self, minimum: int) -> Formula:
        token = self._peek()
        if token is None:
            raise LloydError("unexpected end of formula")
        self.pos += 1
        if token == "not":
            left = Formula("imp", left=self._expr(50), right=Formula("false"))
        elif token == "(":
            left = self._expr(0)
            if self._peek() != ")":
                raise LloydError("expected ')' in formula")
            self.pos += 1
        elif token == "True":
            left = Formula("true")
        elif token == "False":
            left = Formula("false")
        elif re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", token):
            if token in {"and", "or"}:
                raise LloydError(f"operator {token!r} cannot appear here")
            left = Formula("atom", name=token)
        else:
            raise LloydError(f"unexpected formula token {token!r}")

        while (op := self._peek()) in self.PRECEDENCE and self.PRECEDENCE[op] >= minimum:
            precedence = self.PRECEDENCE[op]
            self.pos += 1
            # Implication and equivalence associate to the right; and/or to the left.
            next_minimum = precedence if op in {"->", "<->"} else precedence + 1
            right = self._expr(next_minimum)
            tag = {
                "and": "and", "/\\": "and",
                "or": "or", "\\/": "or",
                "->": "imp", "<->": "iff",
            }[op]
            left = Formula(tag, left=left, right=right)
        return left


def parse_formula(source: str) -> Formula:
    return FormulaParser(source).parse()


# ---------- Proof-term syntax ----------

@dataclass(frozen=True)
class ProofTerm:
    name: str
    args: tuple[ProofTerm | str | Formula, ...] = ()


PROOF_TOKEN = re.compile(r'"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z0-9_.]*|[(),]')


class ProofParser:
    def __init__(self, source: str):
        self.source = source.strip()
        self.tokens: list[str] = []
        pos = 0
        while pos < len(self.source):
            if self.source[pos].isspace():
                pos += 1
                continue
            match = PROOF_TOKEN.match(self.source, pos)
            if not match:
                raise LloydError(f"unsupported proof-term character {self.source[pos]!r}")
            self.tokens.append(match.group(0))
            pos = match.end()
        self.pos = 0

    def parse(self) -> ProofTerm:
        term = self._term()
        if self.pos != len(self.tokens):
            raise LloydError(f"unexpected proof-term token {self.tokens[self.pos]!r}")
        if isinstance(term, Formula):
            raise LloydError("formula(...) is only valid as a proof-function argument")
        return term

    def _term(self) -> ProofTerm | Formula:
        if self.pos >= len(self.tokens):
            raise LloydError("expected a proof term")
        name = self.tokens[self.pos]
        if name == "(":
            self.pos += 1
            nested = self._term()
            if self._peek() != ")":
                raise LloydError("expected ')' in proof term")
            self.pos += 1
            return nested
        self.pos += 1
        if name.startswith('"'):
            raise LloydError("a string is only valid as a function argument")
        name = {"AndIntro": "and_intro"}.get(name, name)
        if self.pos >= len(self.tokens) or self.tokens[self.pos] != "(":
            if name == "and_intro" and self.pos < len(self.tokens) and self._peek() not in {",", ")"}:
                first = self._term()
                second = self._term()
                return ProofTerm(name, (first, second))
            return ProofTerm(name)
        self.pos += 1
        args: list[ProofTerm | str | Formula] = []
        if self._peek() != ")":
            while True:
                if self._peek() and self._peek().startswith('"'):
                    raw = self.tokens[self.pos]
                    self.pos += 1
                    try:
                        args.append(json.loads(raw))
                    except json.JSONDecodeError as exc:
                        raise LloydError(f"invalid string argument: {exc.msg}") from None
                elif name == "formula":
                    raise LloydError('formula arguments must be quoted, for example formula("P -> Q")')
                else:
                    args.append(self._term())
                if self._peek() == ",":
                    self.pos += 1
                    continue
                break
        if self._peek() != ")":
            raise LloydError("expected ')' in proof term")
        self.pos += 1
        if name == "formula":
            if len(args) != 1 or not isinstance(args[0], str):
                raise LloydError('formula expects one quoted string, for example formula("P")')
            return parse_formula(args[0])
        return ProofTerm(name, tuple(args))

    def _peek(self) -> str | None:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None


def parse_proof_term(source: str) -> ProofTerm:
    source = source.strip()
    # The surface form used in LRS examples is an explicit implication binder.
    intro = re.fullmatch(rf"intro\s+({NAME})\s*:\s*(.+?)\s*=>\s*(.+)", source, re.DOTALL)
    if intro:
        binder, formula_text, body_text = intro.groups()
        body = body_text.strip()
        if body.startswith("(") and body.endswith(")"):
            body = body[1:-1].strip()
        return ProofTerm("imp_intro", (binder, parse_formula(formula_text), parse_proof_term(body)))
    return ProofParser(source).parse()


# ---------- Source syntax ----------

NAME = r"[A-Za-z_][A-Za-z0-9_.]*"
AXIOM_RE = re.compile(rf"^Axiom\s+({NAME})\s*:\s*(.+)$")
THEOREM_RE = re.compile(rf"^Theorem\s+({NAME})\.$")
THEOREM_INLINE_RE = re.compile(rf"^Theorem\s+({NAME})\s*:\s*(.+)$")
CLAIM_RE = re.compile(r"^Claim\s*:\s*(.+)$")
STEP_RE = re.compile(rf"^Step\s+({NAME})\s*:\s*(.+),\s*by\s*\[(.*)\]\.$")
HENCE_RE = re.compile(r"^Hence\s+(.+)\s+by\s*\[(.*)\]\.$")
PRINT_RE = re.compile(rf"^Print\s+axioms\s+({NAME})\.?$")


@dataclass
class Theorem:
    name: str
    claim: Formula
    proof: list[tuple[int, str]]
    line: int


@dataclass
class Program:
    axioms: dict[str, Formula]
    theorems: list[Theorem]
    print_requests: list[tuple[int, str]]


def _formula_at(source: str, line: int) -> Formula:
    try:
        return parse_formula(source)
    except LloydError as exc:
        raise LloydError(exc.message, line) from None


def _proof_at(source: str, line: int) -> ProofTerm:
    try:
        return parse_proof_term(source)
    except LloydError as exc:
        raise LloydError(exc.message, line) from None


def _clean_surface_line(source: str) -> str:
    line = source.strip()
    while line.endswith("\\"):
        line = line[:-1].rstrip()
    return line


def _strip_final_period(source: str) -> str:
    source = source.strip()
    return source[:-1].rstrip() if source.endswith(".") else source


def parse_program(text: str) -> Program:
    lines = text.splitlines()
    axioms: dict[str, Formula] = {}
    theorems: list[Theorem] = []
    print_requests: list[tuple[int, str]] = []
    declared: set[str] = set()
    i = 0

    def take_nonempty(index: int) -> tuple[int, str]:
        while index < len(lines) and not _clean_surface_line(lines[index]):
            index += 1
        if index >= len(lines):
            raise LloydError("unexpected end of file", len(lines) or 1)
        return index, _clean_surface_line(lines[index])

    while True:
        i, line = take_nonempty(i) if any(_clean_surface_line(x) for x in lines[i:]) else (len(lines), "")
        if i >= len(lines):
            break
        if m := AXIOM_RE.fullmatch(line):
            name, formula_text = m.groups()
            if name in declared:
                raise LloydError(f"duplicate declaration {name!r}", i + 1)
            axioms[name] = _formula_at(_strip_final_period(formula_text), i + 1)
            declared.add(name)
            i += 1
            continue
        if m := PRINT_RE.fullmatch(line):
            print_requests.append((i + 1, m.group(1)))
            i += 1
            continue
        inline_theorem = THEOREM_INLINE_RE.fullmatch(line)
        separate_theorem = THEOREM_RE.fullmatch(line)
        if inline_theorem or separate_theorem:
            if inline_theorem:
                name, inline_claim = inline_theorem.groups()
                claim = _formula_at(_strip_final_period(inline_claim), i + 1)
            else:
                name = separate_theorem.group(1)
                claim = None
            if name in declared:
                raise LloydError(f"duplicate declaration {name!r}", i + 1)
            theorem_line = i + 1
            declared.add(name)
            if claim is None:
                i, claim_line = take_nonempty(i + 1)
                claim_match = CLAIM_RE.fullmatch(claim_line)
                if not claim_match:
                    raise LloydError("expected 'Claim: FORMULA.' after theorem name", i + 1)
                claim = _formula_at(_strip_final_period(claim_match.group(1)), i + 1)
            i, proof_line = take_nonempty(i + 1)
            if proof_line not in {"Proof", "Proof."}:
                raise LloydError("expected 'Proof' after theorem claim", i + 1)
            proof: list[tuple[int, str]] = []
            i += 1
            saw_qed = False
            while i < len(lines):
                current = _clean_surface_line(lines[i])
                if not current:
                    i += 1
                    continue
                if current in {".", "QED", "QED."}:
                    saw_qed = True
                    i += 1
                    break
                if current == "Todo.":
                    proof.append((i + 1, current))
                    i += 1
                    continue
                if STEP_RE.fullmatch(current) or HENCE_RE.fullmatch(current):
                    proof.append((i + 1, current))
                    i += 1
                    continue
                # A bare proof term is the theorem's explicit final evidence.
                proof.append((i + 1, current))
                i += 1
            if not saw_qed:
                raise LloydError("theorem proof is missing its closing '.'", theorem_line)
            theorems.append(Theorem(name, claim, proof, theorem_line))
            continue
        raise LloydError("expected Axiom, Theorem, or Print axioms", i + 1)

    return Program(axioms, theorems, print_requests)


# ---------- Small trusted checker ----------

@dataclass
class CheckedProgram:
    axioms: dict[str, Formula]
    theorem_claims: dict[str, Formula]
    theorem_dependencies: dict[str, set[str]]
    incomplete: set[str]
    reports: list[str]


def _expect_arity(term: ProofTerm, count: int) -> None:
    if len(term.args) != count:
        raise LloydError(f"{term.name} expects {count} argument(s), got {len(term.args)}")


def _as_term(value: ProofTerm | str | Formula, function: str) -> ProofTerm:
    if not isinstance(value, ProofTerm):
        raise LloydError(f"argument to {function} must be a proof term")
    return value


def _as_name(value: ProofTerm | str | Formula, function: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(NAME, value):
        raise LloydError(f"argument to {function} must be a quoted name")
    return value


def _as_formula(value: ProofTerm | str | Formula, function: str) -> Formula:
    if not isinstance(value, Formula):
        raise LloydError(f"argument to {function} must be formula(\"...\")")
    return value


def _arrow(left: Formula, right: Formula) -> Formula:
    return Formula("imp", left=left, right=right)


class Kernel:
    def __init__(self, axioms: dict[str, Formula]):
        self.axioms = dict(axioms)
        self.theorem_claims: dict[str, Formula] = {}
        self.theorem_dependencies: dict[str, set[str]] = {}
        self.incomplete: set[str] = set()

    def infer(
        self,
        term: ProofTerm,
        local: dict[str, Formula],
        globals_: dict[str, Formula],
        dependencies: set[str],
        line: int,
    ) -> Formula:
        try:
            if term.name == "$formula":
                raise LloydError("formula(...) is only valid as an argument")
            if term.name not in {
                "imp_intro", "imp_apply", "and_intro", "and_left", "and_right",
                "or_left", "or_right", "or_cases", "false_elim", "iff_intro",
                "iff_left", "iff_right",
            }:
                if term.args:
                    raise LloydError(f"unknown proof function {term.name!r}")
                if term.name in local:
                    return local[term.name]
                if term.name in globals_:
                    dependencies.add(term.name)
                    return globals_[term.name]
                for suffix, component in ((".1", 0), (".2", 1)):
                    if term.name.endswith(suffix):
                        pair_name = term.name[:-len(suffix)]
                        if pair_name in local:
                            pair = local[pair_name]
                        elif pair_name in globals_:
                            dependencies.add(pair_name)
                            pair = globals_[pair_name]
                        else:
                            continue
                        if pair.tag != "and":
                            raise LloydError(f"projection {term.name!r} requires a proof of P /\\ Q")
                        result = pair.left if component == 0 else pair.right
                        assert result is not None
                        return result
                if term.name in self.incomplete:
                    raise LloydError(f"{term.name!r} is incomplete and cannot be referenced")
                for suffix in (".1", ".2"):
                    if term.name.endswith(suffix) and term.name[:-len(suffix)] in self.incomplete:
                        raise LloydError(f"{term.name[:-len(suffix)]!r} is incomplete and cannot be referenced")
                raise LloydError(f"unknown proof name {term.name!r}")

            args = term.args
            if term.name == "imp_intro":
                _expect_arity(term, 3)
                name = _as_name(args[0], term.name)
                premise = _as_formula(args[1], term.name)
                body = _as_term(args[2], term.name)
                if name in local or name in globals_:
                    raise LloydError(f"local name {name!r} is already in scope")
                nested = dict(local)
                nested[name] = premise
                conclusion = self.infer(body, nested, globals_, dependencies, line)
                return _arrow(premise, conclusion)

            if term.name == "imp_apply":
                _expect_arity(term, 2)
                function = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                argument = self.infer(_as_term(args[1], term.name), local, globals_, dependencies, line)
                if function.tag != "imp" or function.left != argument:
                    raise LloydError(f"imp_apply expected a proof of {function.left if function.tag == 'imp' else 'P -> Q'} and received {argument}")
                assert function.right is not None
                return function.right

            if term.name == "and_intro":
                _expect_arity(term, 2)
                left = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                right = self.infer(_as_term(args[1], term.name), local, globals_, dependencies, line)
                return Formula("and", left=left, right=right)

            if term.name in {"and_left", "and_right"}:
                _expect_arity(term, 1)
                pair = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                if pair.tag != "and":
                    raise LloydError(f"{term.name} requires a proof of P and Q, received {pair}")
                result = pair.left if term.name == "and_left" else pair.right
                assert result is not None
                return result

            if term.name in {"or_left", "or_right"}:
                _expect_arity(term, 2)
                if term.name == "or_left":
                    proof = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                    other = _as_formula(args[1], term.name)
                    return Formula("or", left=proof, right=other)
                other = _as_formula(args[0], term.name)
                proof = self.infer(_as_term(args[1], term.name), local, globals_, dependencies, line)
                return Formula("or", left=other, right=proof)

            if term.name == "or_cases":
                _expect_arity(term, 5)
                disjunction = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                if disjunction.tag != "or":
                    raise LloydError(f"or_cases requires a proof of P or Q, received {disjunction}")
                left_name = _as_name(args[1], term.name)
                left_proof = _as_term(args[2], term.name)
                right_name = _as_name(args[3], term.name)
                right_proof = _as_term(args[4], term.name)
                assert disjunction.left is not None and disjunction.right is not None
                if left_name in local or left_name in globals_ or right_name in local or right_name in globals_:
                    raise LloydError("or_cases branch names must be fresh in their scope")
                left_context = dict(local)
                right_context = dict(local)
                left_context[left_name] = disjunction.left
                right_context[right_name] = disjunction.right
                left_result = self.infer(left_proof, left_context, globals_, dependencies, line)
                right_result = self.infer(right_proof, right_context, globals_, dependencies, line)
                if left_result != right_result:
                    raise LloydError(f"or_cases branches disagree: {left_result} versus {right_result}")
                return left_result

            if term.name == "false_elim":
                _expect_arity(term, 2)
                contradiction = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                target = _as_formula(args[1], term.name)
                if contradiction.tag != "false":
                    raise LloydError(f"false_elim requires a proof of False, received {contradiction}")
                return target

            if term.name == "iff_intro":
                _expect_arity(term, 2)
                forward = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                backward = self.infer(_as_term(args[1], term.name), local, globals_, dependencies, line)
                if forward.tag != "imp" or backward.tag != "imp":
                    raise LloydError("iff_intro expects proofs of P -> Q and Q -> P")
                if forward.left != backward.right or forward.right != backward.left:
                    raise LloydError(f"iff_intro directions do not match: {forward} and {backward}")
                assert forward.left is not None and forward.right is not None
                return Formula("iff", left=forward.left, right=forward.right)

            if term.name in {"iff_left", "iff_right"}:
                _expect_arity(term, 1)
                iff = self.infer(_as_term(args[0], term.name), local, globals_, dependencies, line)
                if iff.tag != "iff":
                    raise LloydError(f"{term.name} requires a proof of P <-> Q, received {iff}")
                assert iff.left is not None and iff.right is not None
                if term.name == "iff_left":
                    return _arrow(iff.left, iff.right)
                return _arrow(iff.right, iff.left)

            raise LloydError(f"unsupported proof function {term.name!r}")
        except LloydError as exc:
            if exc.line is not None:
                raise
            raise LloydError(exc.message, line) from None

    def check(self, program: Program) -> CheckedProgram:
        globals_: dict[str, Formula] = dict(self.axioms)
        for theorem in program.theorems:
            local: dict[str, Formula] = {}
            dependencies: set[str] = set()
            saw_todo = False
            saw_hence = False
            for line_number, sentence in theorem.proof:
                if sentence == "Todo.":
                    if saw_hence:
                        raise LloydError("Todo cannot follow the final Hence", line_number)
                    saw_todo = True
                    continue
                if m := STEP_RE.fullmatch(sentence):
                    if saw_hence:
                        raise LloydError("no proof sentence may follow the final Hence", line_number)
                    name, formula_text, proof_text = m.groups()
                    if name in local or name in globals_:
                        raise LloydError(f"duplicate or shadowing proof name {name!r}", line_number)
                    expected = _formula_at(formula_text, line_number)
                    proof = _proof_at(proof_text, line_number)
                    actual = self.infer(proof, local, globals_, dependencies, line_number)
                    if actual != expected:
                        raise LloydError(f"step {name!r} claims {expected}, but its proof has type {actual}", line_number)
                    local[name] = expected
                    continue
                if m := HENCE_RE.fullmatch(sentence):
                    if saw_hence:
                        raise LloydError("a theorem may contain only one final Hence", line_number)
                    formula_text, proof_text = m.groups()
                    expected = _formula_at(formula_text, line_number)
                    proof = _proof_at(proof_text, line_number)
                    actual = self.infer(proof, local, globals_, dependencies, line_number)
                    if actual != expected:
                        raise LloydError(f"Hence claims {expected}, but its proof has type {actual}", line_number)
                    if expected != theorem.claim:
                        raise LloydError(f"final Hence proves {expected}, but theorem claim is {theorem.claim}", line_number)
                    saw_hence = True
                    continue
                if saw_hence:
                    raise LloydError("no proof sentence may follow the final proof term", line_number)
                proof = _proof_at(sentence, line_number)
                actual = self.infer(proof, local, globals_, dependencies, line_number)
                if actual != theorem.claim:
                    raise LloydError(f"proof term has type {actual}, but theorem claim is {theorem.claim}", line_number)
                saw_hence = True
            if saw_todo:
                self.incomplete.add(theorem.name)
                self.theorem_claims[theorem.name] = theorem.claim
                self.theorem_dependencies[theorem.name] = dependencies
                continue
            if not saw_hence:
                raise LloydError("completed theorem needs one final Hence; use Todo. for an unfinished theorem", theorem.line)
            self.theorem_claims[theorem.name] = theorem.claim
            self.theorem_dependencies[theorem.name] = dependencies
            globals_[theorem.name] = theorem.claim

        reports: list[str] = []
        for line_number, name in program.print_requests:
            if name not in globals_ and name not in self.theorem_claims:
                raise LloydError(f"unknown theorem or axiom {name!r}", line_number)
            found: set[str] = set()
            seen: set[str] = set()

            def visit(item: str) -> None:
                if item in seen:
                    return
                seen.add(item)
                if item in self.axioms:
                    found.add(item)
                for dependency in self.theorem_dependencies.get(item, set()):
                    visit(dependency)

            visit(name)
            unfinished = sorted(x for x in seen if x in self.incomplete)
            axiom_names = ", ".join(sorted(found)) if found else "none"
            unfinished_names = ", ".join(unfinished) if unfinished else "none"
            reports.append(f"{name}: axioms = {axiom_names}; unfinished = {unfinished_names}")

        return CheckedProgram(
            axioms=self.axioms,
            theorem_claims=self.theorem_claims,
            theorem_dependencies=self.theorem_dependencies,
            incomplete=self.incomplete,
            reports=reports,
        )


# ---------- CLI ----------

def run_check(path: Path) -> int:
    try:
        source = path.read_text(encoding="utf-8")
        program = parse_program(source)
        result = Kernel(program.axioms).check(program)
    except (OSError, UnicodeError) as exc:
        print(f"lloyd: {exc}", file=sys.stderr)
        return 2
    except LloydError as exc:
        print(f"lloyd: {exc}", file=sys.stderr)
        return 1

    for name, claim in result.theorem_claims.items():
        print(f"checked: {name}: {claim}")
    for name in sorted(result.incomplete):
        print(f"incomplete: {name}")
    for report in result.reports:
        print(report)
    if result.incomplete:
        print("file is not certified because it contains unfinished theorems")
        return 1
    print("file certified for the supported propositional fragment")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lloyd",
        description="Check the explicit intuitionistic propositional fragment of Lloyd LRS-Alpha.",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    check_parser = subparsers.add_parser("check", help="check one .lloyd source file")
    check_parser.add_argument("file", type=Path)
    args = parser.parse_args(argv)
    if args.command == "check":
        return run_check(args.file)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
