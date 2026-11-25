/*
 * Lloyd LRS-Alpha propositional checker, portable C11 edition.
 *
 * This is a C port of the existing Python checker's supported fragment. It
 * deliberately does not certify equality, arithmetic, induction, definitions,
 *imports, dependent types, or the indentation-based natural-number example.
 
 
 *SPDX-License-Identifier: BSD-3-Clause
 *Copyright (c) 2026 97neko75
 */
#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum { F_ATOM, F_TRUE, F_FALSE, F_AND, F_OR, F_IMP, F_IFF } FKind;
typedef struct Formula Formula;
struct Formula {
    FKind kind;
    char *name;
    Formula *left;
    Formula *right;
};

typedef enum { ARG_TERM, ARG_NAME, ARG_FORMULA } ArgKind;
typedef struct ProofTerm ProofTerm;
typedef struct {
    ArgKind kind;
    ProofTerm *term;
    char *name;
    Formula *formula;
} ProofArg;
struct ProofTerm {
    char *name;
    ProofArg *args;
    size_t argc;
};

typedef struct { char *text; int line; } SourceLine;
typedef struct { char *name; Formula *formula; int line; } Axiom;
typedef struct { int line; char *text; } ProofLine;
typedef struct {
    char *name;
    Formula *claim;
    ProofLine *proof;
    size_t proof_count;
    size_t proof_capacity;
    char **dependencies;
    size_t dependency_count;
    size_t dependency_capacity;
    int line;
    int incomplete;
    int checked;
} Theorem;
typedef struct { int line; char *name; } PrintRequest;
typedef struct {
    Axiom *axioms;
    size_t axiom_count;
    size_t axiom_capacity;
    Theorem *theorems;
    size_t theorem_count;
    size_t theorem_capacity;
    PrintRequest *prints;
    size_t print_count;
    size_t print_capacity;
} Program;

typedef struct { char *data; size_t length; size_t capacity; } StringBuilder;
typedef struct { const char *source; size_t pos; int line; } FormulaParser;
typedef enum { PT_IDENT, PT_STRING, PT_LPAREN, PT_RPAREN, PT_COMMA } PTokKind;
typedef struct { PTokKind kind; char *text; } PTok;
typedef struct {
    PTok *tokens;
    size_t count;
    size_t capacity;
    size_t pos;
    int line;
} ProofParser;
typedef struct { char *name; Formula *formula; } Binding;
typedef struct { Binding *items; size_t count; size_t capacity; } Context;

static char g_error[1024];
static int g_error_line;

static void *xmalloc(size_t size) {
    void *p = malloc(size ? size : 1);
    if (!p) {
        fputs("lloyd: out of memory\n", stderr);
        exit(2);
    }
    return p;
}

static void *xrealloc(void *old, size_t size) {
    void *p = realloc(old, size ? size : 1);
    if (!p) {
        fputs("lloyd: out of memory\n", stderr);
        exit(2);
    }
    return p;
}

static char *copy_n(const char *s, size_t n) {
    char *out = (char *)xmalloc(n + 1);
    memcpy(out, s, n);
    out[n] = '\0';
    return out;
}

static char *copy_s(const char *s) { return copy_n(s, strlen(s)); }

static void set_error(int line, const char *fmt, ...) {
    va_list args;
    if (g_error[0]) return;
    g_error_line = line;
    va_start(args, fmt);
    vsnprintf(g_error, sizeof g_error, fmt, args);
    va_end(args);
}

static void reserve_array(void **array, size_t *capacity, size_t count, size_t item_size) {
    size_t next;
    if (count <= *capacity) return;
    next = *capacity ? *capacity : 8;
    while (next < count) {
        if (next > ((size_t)-1) / 2) {
            fputs("lloyd: input is too large\n", stderr);
            exit(2);
        }
        next *= 2;
    }
    *array = xrealloc(*array, next * item_size);
    *capacity = next;
}

static char *trim_copy(const char *s) {
    const char *begin = s;
    const char *end;
    while (*begin && isspace((unsigned char)*begin)) begin++;
    end = begin + strlen(begin);
    while (end > begin && isspace((unsigned char)end[-1])) end--;
    return copy_n(begin, (size_t)(end - begin));
}

static int is_ident_start(unsigned char c) { return isalpha(c) || c == '_'; }
static int is_ident_part(unsigned char c) { return isalnum(c) || c == '_' || c == '.'; }

static int valid_name(const char *s) {
    size_t i = 0;
    if (!s[0] || !is_ident_start((unsigned char)s[0])) return 0;
    for (i = 1; s[i]; i++) if (!is_ident_part((unsigned char)s[i])) return 0;
    return 1;
}

static Formula *new_formula(FKind kind, const char *name, Formula *left, Formula *right) {
    Formula *f = (Formula *)xmalloc(sizeof *f);
    f->kind = kind;
    f->name = name ? copy_s(name) : NULL;
    f->left = left;
    f->right = right;
    return f;
}

static int formula_equal(const Formula *a, const Formula *b) {
    if (a == b) return 1;
    if (!a || !b || a->kind != b->kind) return 0;
    if (a->kind == F_ATOM) return strcmp(a->name, b->name) == 0;
    if (a->kind == F_TRUE || a->kind == F_FALSE) return 1;
    return formula_equal(a->left, b->left) && formula_equal(a->right, b->right);
}

static void sb_init(StringBuilder *sb) { sb->data = NULL; sb->length = 0; sb->capacity = 0; }
static void sb_append_n(StringBuilder *sb, const char *s, size_t n) {
    reserve_array((void **)&sb->data, &sb->capacity, sb->length + n + 1, 1);
    memcpy(sb->data + sb->length, s, n);
    sb->length += n;
    sb->data[sb->length] = '\0';
}
static void sb_append(StringBuilder *sb, const char *s) { sb_append_n(sb, s, strlen(s)); }

static void format_formula_into(StringBuilder *sb, const Formula *f) {
    if (!f) { sb_append(sb, "<null>"); return; }
    switch (f->kind) {
        case F_ATOM: sb_append(sb, f->name); return;
        case F_TRUE: sb_append(sb, "True"); return;
        case F_FALSE: sb_append(sb, "False"); return;
        case F_AND:
        case F_OR:
        case F_IMP:
        case F_IFF:
            if (f->kind == F_IMP && f->right && f->right->kind == F_FALSE) {
                int needs_parens = f->left && (f->left->kind == F_IMP || f->left->kind == F_IFF || f->left->kind == F_OR);
                sb_append(sb, "not ");
                if (needs_parens) sb_append(sb, "(");
                format_formula_into(sb, f->left);
                if (needs_parens) sb_append(sb, ")");
                return;
            }
            sb_append(sb, "(");
            format_formula_into(sb, f->left);
            sb_append(sb, f->kind == F_AND ? " and " : f->kind == F_OR ? " or " : f->kind == F_IMP ? " -> " : " <-> ");
            format_formula_into(sb, f->right);
            sb_append(sb, ")");
            return;
    }
}

static char *format_formula(const Formula *f) {
    StringBuilder sb;
    sb_init(&sb);
    format_formula_into(&sb, f);
    if (!sb.data) return copy_s("");
    return sb.data;
}

static void formula_skip_space(FormulaParser *p) {
    while (p->source[p->pos] && isspace((unsigned char)p->source[p->pos])) p->pos++;
}

static int word_at(const char *s, size_t pos, const char *word) {
    size_t n = strlen(word);
    if (strncmp(s + pos, word, n) != 0) return 0;
    return !is_ident_part((unsigned char)s[pos + n]);
}

static Formula *parse_formula_expr(FormulaParser *p, int minimum);

static Formula *parse_formula_prefix(FormulaParser *p) {
    size_t start;
    Formula *inner;
    formula_skip_space(p);
    if (!p->source[p->pos]) {
        set_error(p->line, "unexpected end of formula");
        return NULL;
    }
    if (word_at(p->source, p->pos, "not")) {
        p->pos += 3;
        inner = parse_formula_expr(p, 50);
        if (!inner) return NULL;
        return new_formula(F_IMP, NULL, inner, new_formula(F_FALSE, NULL, NULL, NULL));
    }
    if (p->source[p->pos] == '(') {
        p->pos++;
        inner = parse_formula_expr(p, 0);
        if (!inner) return NULL;
        formula_skip_space(p);
        if (p->source[p->pos] != ')') {
            set_error(p->line, "expected ')' in formula");
            return NULL;
        }
        p->pos++;
        return inner;
    }
    if (word_at(p->source, p->pos, "True")) {
        p->pos += 4;
        return new_formula(F_TRUE, NULL, NULL, NULL);
    }
    if (word_at(p->source, p->pos, "False")) {
        p->pos += 5;
        return new_formula(F_FALSE, NULL, NULL, NULL);
    }
    if (!is_ident_start((unsigned char)p->source[p->pos])) {
        set_error(p->line, "unexpected formula character '%c'", p->source[p->pos]);
        return NULL;
    }
    start = p->pos++;
    while (is_ident_part((unsigned char)p->source[p->pos])) p->pos++;
    {
        char *name = copy_n(p->source + start, p->pos - start);
        if (strcmp(name, "and") == 0 || strcmp(name, "or") == 0) {
            set_error(p->line, "operator '%s' cannot appear here", name);
            return NULL;
        }
        return new_formula(F_ATOM, name, NULL, NULL);
    }
}

typedef struct { const char *text; size_t length; int precedence; FKind kind; int right_associative; } FOperator;

static int formula_operator_at(FormulaParser *p, FOperator *op) {
    const char *s = p->source + p->pos;
    formula_skip_space(p);
    s = p->source + p->pos;
    if (strncmp(s, "<->", 3) == 0) { op->text = "<->"; op->length = 3; op->precedence = 10; op->kind = F_IFF; op->right_associative = 1; return 1; }
    if (strncmp(s, "->", 2) == 0) { op->text = "->"; op->length = 2; op->precedence = 20; op->kind = F_IMP; op->right_associative = 1; return 1; }
    if (strncmp(s, "/\\", 2) == 0) { op->text = "/\\"; op->length = 2; op->precedence = 40; op->kind = F_AND; op->right_associative = 0; return 1; }
    if (strncmp(s, "\\/", 2) == 0) { op->text = "\\/"; op->length = 2; op->precedence = 30; op->kind = F_OR; op->right_associative = 0; return 1; }
    if (word_at(s, 0, "and")) { op->text = "and"; op->length = 3; op->precedence = 40; op->kind = F_AND; op->right_associative = 0; return 1; }
    if (word_at(s, 0, "or")) { op->text = "or"; op->length = 2; op->precedence = 30; op->kind = F_OR; op->right_associative = 0; return 1; }
    return 0;
}

static Formula *parse_formula_expr(FormulaParser *p, int minimum) {
    Formula *left = parse_formula_prefix(p);
    FOperator op;
    if (!left) return NULL;
    for (;;) {
        size_t saved = p->pos;
        if (!formula_operator_at(p, &op) || op.precedence < minimum) {
            p->pos = saved;
            break;
        }
        p->pos += op.length;
        {
            Formula *right = parse_formula_expr(p, op.right_associative ? op.precedence : op.precedence + 1);
            if (!right) return NULL;
            left = new_formula(op.kind, NULL, left, right);
        }
    }
    return left;
}

static Formula *parse_formula(const char *source, int line) {
    FormulaParser p;
    Formula *result;
    p.source = source;
    p.pos = 0;
    p.line = line;
    result = parse_formula_expr(&p, 0);
    if (!result) return NULL;
    formula_skip_space(&p);
    if (p.source[p.pos]) {
        set_error(line, "unexpected formula token near '%s'", p.source + p.pos);
        return NULL;
    }
    return result;
}

static void proof_push_token(ProofParser *p, PTokKind kind, char *text) {
    reserve_array((void **)&p->tokens, &p->capacity, p->count + 1, sizeof *p->tokens);
    p->tokens[p->count].kind = kind;
    p->tokens[p->count].text = text;
    p->count++;
}

static int tokenize_proof(ProofParser *p, const char *source) {
    size_t i = 0;
    memset(p, 0, sizeof *p);
    p->line = 0;
    while (source[i]) {
        unsigned char c = (unsigned char)source[i];
        if (isspace(c)) { i++; continue; }
        if (c == '(') { proof_push_token(p, PT_LPAREN, NULL); i++; continue; }
        if (c == ')') { proof_push_token(p, PT_RPAREN, NULL); i++; continue; }
        if (c == ',') { proof_push_token(p, PT_COMMA, NULL); i++; continue; }
        if (c == '"') {
            StringBuilder sb;
            sb_init(&sb);
            i++;
            while (source[i] && source[i] != '"') {
                if (source[i] == '\\') {
                    i++;
                    if (!source[i]) { set_error(p->line, "unterminated escape in proof string"); return 0; }
                    switch (source[i]) {
                        case 'n': sb_append(&sb, "\n"); break;
                        case 'r': sb_append(&sb, "\r"); break;
                        case 't': sb_append(&sb, "\t"); break;
                        case '"': sb_append(&sb, "\""); break;
                        case '\\': sb_append(&sb, "\\"); break;
                        default: set_error(p->line, "unsupported escape in proof string"); return 0;
                    }
                    i++;
                } else {
                    sb_append_n(&sb, source + i, 1);
                    i++;
                }
            }
            if (!source[i]) { set_error(p->line, "unterminated string in proof term"); return 0; }
            i++;
            proof_push_token(p, PT_STRING, sb.data ? sb.data : copy_s(""));
            continue;
        }
        if (is_ident_start(c)) {
            size_t start = i++;
            while (is_ident_part((unsigned char)source[i])) i++;
            proof_push_token(p, PT_IDENT, copy_n(source + start, i - start));
            continue;
        }
        set_error(p->line, "unsupported proof-term character '%c'", source[i]);
        return 0;
    }
    return 1;
}

static ProofTerm *new_proof_term(const char *name) {
    ProofTerm *t = (ProofTerm *)xmalloc(sizeof *t);
    t->name = copy_s(name);
    t->args = NULL;
    t->argc = 0;
    return t;
}

static void proof_add_arg(ProofTerm *t, ProofArg arg) {
    t->args = (ProofArg *)xrealloc(t->args, (t->argc + 1) * sizeof *t->args);
    t->args[t->argc++] = arg;
}

static PTok *proof_peek(ProofParser *p) { return p->pos < p->count ? &p->tokens[p->pos] : NULL; }
static ProofTerm *proof_parse_recursive(ProofParser *p);

static Formula *parse_formula_string(const char *s, int line) {
    g_error_line = 0;
    return parse_formula(s, line);
}

static ProofTerm *proof_parse_recursive(ProofParser *p) {
    PTok *tok = proof_peek(p);
    char *name;
    ProofTerm *term;
    if (!tok) { set_error(p->line, "expected a proof term"); return NULL; }
    if (tok->kind == PT_LPAREN) {
        p->pos++;
        term = proof_parse_recursive(p);
        tok = proof_peek(p);
        if (!tok || tok->kind != PT_RPAREN) { set_error(p->line, "expected ')' in proof term"); return NULL; }
        p->pos++;
        return term;
    }
    if (tok->kind != PT_IDENT) {
        set_error(p->line, tok->kind == PT_STRING ? "a string is only valid as a function argument" : "expected a proof name");
        return NULL;
    }
    name = tok->text;
    p->pos++;
    if (strcmp(name, "formula") == 0) {
        PTok *str;
        Formula *f;
        tok = proof_peek(p);
        if (!tok || tok->kind != PT_LPAREN) { set_error(p->line, "formula expects one quoted string"); return NULL; }
        p->pos++;
        str = proof_peek(p);
        if (!str || str->kind != PT_STRING) { set_error(p->line, "formula expects one quoted string"); return NULL; }
        p->pos++;
        tok = proof_peek(p);
        if (!tok || tok->kind != PT_RPAREN) { set_error(p->line, "expected ')' after formula string"); return NULL; }
        p->pos++;
        f = parse_formula_string(str->text, p->line);
        if (!f) return NULL;
        term = new_proof_term("$formula");
        {
            ProofArg arg;
            memset(&arg, 0, sizeof arg);
            arg.kind = ARG_FORMULA;
            arg.formula = f;
            proof_add_arg(term, arg);
        }
        return term;
    }
    if (strcmp(name, "AndIntro") == 0) name = "and_intro";
    term = new_proof_term(name);
    tok = proof_peek(p);
    if (tok && tok->kind == PT_LPAREN) {
        p->pos++;
        tok = proof_peek(p);
        if (!tok) { set_error(p->line, "expected ')' in proof term"); return NULL; }
        if (tok->kind != PT_RPAREN) {
            for (;;) {
                ProofArg arg;
                memset(&arg, 0, sizeof arg);
                tok = proof_peek(p);
                if (tok && tok->kind == PT_STRING) {
                    arg.kind = ARG_NAME;
                    arg.name = tok->text;
                    p->pos++;
                } else {
                    arg.kind = ARG_TERM;
                    arg.term = proof_parse_recursive(p);
                    if (!arg.term) return NULL;
                    if (strcmp(arg.term->name, "$formula") == 0 && arg.term->argc == 1 &&
                        arg.term->args[0].kind == ARG_FORMULA) {
                        arg.kind = ARG_FORMULA;
                        arg.formula = arg.term->args[0].formula;
                    }
                }
                proof_add_arg(term, arg);
                tok = proof_peek(p);
                if (tok && tok->kind == PT_COMMA) { p->pos++; continue; }
                break;
            }
        }
        tok = proof_peek(p);
        if (!tok || tok->kind != PT_RPAREN) { set_error(p->line, "expected ')' in proof term"); return NULL; }
        p->pos++;
        return term;
    }
    if (strcmp(name, "and_intro") == 0 && tok && tok->kind != PT_COMMA && tok->kind != PT_RPAREN) {
        ProofArg a, b;
        memset(&a, 0, sizeof a); memset(&b, 0, sizeof b);
        a.kind = ARG_TERM; a.term = proof_parse_recursive(p);
        b.kind = ARG_TERM; b.term = proof_parse_recursive(p);
        if (!a.term || !b.term) return NULL;
        proof_add_arg(term, a); proof_add_arg(term, b);
    }
    return term;
}

static ProofTerm *parse_proof_term(const char *source, int line) {
    ProofParser p;
    ProofTerm *term;
    char *clean = trim_copy(source);
    size_t n = strlen(clean);
    memset(&p, 0, sizeof p);
    p.line = line;
    if (strncmp(clean, "intro", 5) == 0 && isspace((unsigned char)clean[5])) {
        char *binder = clean + 5;
        char *colon;
        char *arrow;
        char *formula_text;
        char *body_text;
        while (isspace((unsigned char)*binder)) binder++;
        colon = strchr(binder, ':');
        arrow = strstr(colon ? colon + 1 : binder, "=>");
        if (colon && arrow) {
            char *binder_name = trim_copy(copy_n(binder, (size_t)(colon - binder)));
            formula_text = trim_copy(copy_n(colon + 1, (size_t)(arrow - (colon + 1))));
            body_text = trim_copy(arrow + 2);
            n = strlen(body_text);
            if (n >= 2 && body_text[0] == '(' && body_text[n - 1] == ')') {
                body_text[n - 1] = '\0';
                memmove(body_text, body_text + 1, n - 1);
                body_text = trim_copy(body_text);
            }
            if (!valid_name(binder_name)) { set_error(line, "invalid intro binder name"); return NULL; }
            {
                Formula *premise = parse_formula(formula_text, line);
                ProofTerm *body;
                ProofArg a0, a1, a2;
                if (!premise) return NULL;
                body = parse_proof_term(body_text, line);
                if (!body) return NULL;
                term = new_proof_term("imp_intro");
                memset(&a0, 0, sizeof a0); memset(&a1, 0, sizeof a1); memset(&a2, 0, sizeof a2);
                a0.kind = ARG_NAME; a0.name = binder_name;
                a1.kind = ARG_FORMULA; a1.formula = premise;
                a2.kind = ARG_TERM; a2.term = body;
                proof_add_arg(term, a0); proof_add_arg(term, a1); proof_add_arg(term, a2);
                return term;
            }
        }
    }
    if (!tokenize_proof(&p, clean)) return NULL;
    term = proof_parse_recursive(&p);
    if (!term) return NULL;
    if (p.pos != p.count) {
        PTok *t = proof_peek(&p);
        set_error(line, "unexpected proof-term token '%s'", t && t->text ? t->text : "punctuation");
        return NULL;
    }
    if (strcmp(term->name, "$formula") == 0) {
        set_error(line, "formula(...) is only valid as a proof-function argument");
        return NULL;
    }
    return term;
}

static void program_add_axiom(Program *p, Axiom item) {
    reserve_array((void **)&p->axioms, &p->axiom_capacity, p->axiom_count + 1, sizeof *p->axioms);
    p->axioms[p->axiom_count++] = item;
}
static void program_add_theorem(Program *p, Theorem item) {
    reserve_array((void **)&p->theorems, &p->theorem_capacity, p->theorem_count + 1, sizeof *p->theorems);
    p->theorems[p->theorem_count++] = item;
}
static void program_add_print(Program *p, PrintRequest item) {
    reserve_array((void **)&p->prints, &p->print_capacity, p->print_count + 1, sizeof *p->prints);
    p->prints[p->print_count++] = item;
}
static void theorem_add_proof_line(Theorem *t, int line, const char *text) {
    reserve_array((void **)&t->proof, &t->proof_capacity, t->proof_count + 1, sizeof *t->proof);
    t->proof[t->proof_count].line = line;
    t->proof[t->proof_count].text = copy_s(text);
    t->proof_count++;
}

static int find_char_outside(const char *s, char c) {
    int depth = 0;
    int in_string = 0;
    for (int i = 0; s[i]; i++) {
        if (s[i] == '"' && (i == 0 || s[i - 1] != '\\')) in_string = !in_string;
        if (in_string) continue;
        if (s[i] == '(') depth++;
        else if (s[i] == ')' && depth > 0) depth--;
        else if (s[i] == c && depth == 0) return i;
    }
    return -1;
}

static char *remove_final_period(const char *s) {
    char *out = trim_copy(s);
    size_t n = strlen(out);
    if (n && out[n - 1] == '.') { out[n - 1] = '\0'; out = trim_copy(out); }
    return out;
}

static char *clean_source_line(const char *s) {
    char *out = trim_copy(s);
    size_t n;
    while ((n = strlen(out)) && out[n - 1] == '\\') {
        out[n - 1] = '\0';
        out = trim_copy(out);
    }
    return out;
}

static int declaration_exists(const Program *p, const char *name) {
    size_t i;
    for (i = 0; i < p->axiom_count; i++) if (strcmp(p->axioms[i].name, name) == 0) return 1;
    for (i = 0; i < p->theorem_count; i++) if (strcmp(p->theorems[i].name, name) == 0) return 1;
    return 0;
}

static int starts_with(const char *s, const char *prefix) { return strncmp(s, prefix, strlen(prefix)) == 0; }

static int parse_source(Program *program, const char *source) {
    SourceLine *lines = NULL;
    size_t line_count = 0, line_capacity = 0;
    const char *p = source, *start = source;
    int physical_line = 1;
    while (1) {
        if (*p == '\n' || *p == '\0') {
            char *raw = copy_n(start, (size_t)(p - start));
            size_t n = strlen(raw);
            if (n && raw[n - 1] == '\r') raw[n - 1] = '\0';
            reserve_array((void **)&lines, &line_capacity, line_count + 1, sizeof *lines);
            lines[line_count].text = clean_source_line(raw);
            lines[line_count].line = physical_line++;
            line_count++;
            if (!*p) break;
            start = p + 1;
        }
        p++;
    }
    for (size_t i = 0; i < line_count;) {
        char *line = lines[i].text;
        int source_line = lines[i].line;
        if (!line[0]) { i++; continue; }
        if (starts_with(line, "Axiom ")) {
            char *body = trim_copy(line + 6);
            int colon = find_char_outside(body, ':');
            if (colon < 0) { set_error(source_line, "expected 'Axiom NAME : FORMULA'"); return 0; }
            char *name = trim_copy(copy_n(body, (size_t)colon));
            char *formula_text = remove_final_period(body + colon + 1);
            Formula *formula;
            if (!valid_name(name)) { set_error(source_line, "invalid axiom name '%s'", name); return 0; }
            if (declaration_exists(program, name)) { set_error(source_line, "duplicate declaration '%s'", name); return 0; }
            formula = parse_formula(formula_text, source_line);
            if (!formula) return 0;
            {
                Axiom ax;
                ax.name = name; ax.formula = formula; ax.line = source_line;
                program_add_axiom(program, ax);
            }
            i++;
            continue;
        }
        if (starts_with(line, "Print axioms ")) {
            char *name = remove_final_period(line + 13);
            if (!valid_name(name)) { set_error(source_line, "expected theorem or axiom name after 'Print axioms'"); return 0; }
            {
                PrintRequest request;
                request.line = source_line; request.name = name;
                program_add_print(program, request);
            }
            i++;
            continue;
        }
        if (starts_with(line, "Theorem ")) {
            char *body = trim_copy(line + 8);
            char *name;
            Formula *claim = NULL;
            int colon;
            Theorem theorem;
            memset(&theorem, 0, sizeof theorem);
            colon = find_char_outside(body, ':');
            if (colon >= 0) {
                name = trim_copy(copy_n(body, (size_t)colon));
                claim = parse_formula(remove_final_period(body + colon + 1), source_line);
                if (!claim) return 0;
            } else {
                name = remove_final_period(body);
            }
            if (!valid_name(name)) { set_error(source_line, "invalid theorem name '%s'", name); return 0; }
            if (declaration_exists(program, name)) { set_error(source_line, "duplicate declaration '%s'", name); return 0; }
            theorem.name = name;
            theorem.claim = claim;
            theorem.line = source_line;
            i++;
            if (!claim) {
                while (i < line_count && !lines[i].text[0]) i++;
                if (i >= line_count || !starts_with(lines[i].text, "Claim:")) {
                    set_error(i < line_count ? lines[i].line : source_line, "expected 'Claim: FORMULA.' after theorem name");
                    return 0;
                }
                theorem.claim = parse_formula(remove_final_period(trim_copy(lines[i].text + 6)), lines[i].line);
                if (!theorem.claim) return 0;
                i++;
            }
            while (i < line_count && !lines[i].text[0]) i++;
            if (i >= line_count || (strcmp(lines[i].text, "Proof") != 0 && strcmp(lines[i].text, "Proof.") != 0)) {
                set_error(i < line_count ? lines[i].line : source_line, "expected 'Proof' after theorem claim");
                return 0;
            }
            i++;
            {
                int closed = 0;
                while (i < line_count) {
                    char *current = lines[i].text;
                    if (!current[0]) { i++; continue; }
                    if (strcmp(current, ".") == 0 || strcmp(current, "QED") == 0 || strcmp(current, "QED.") == 0) {
                        closed = 1; i++; break;
                    }
                    theorem_add_proof_line(&theorem, lines[i].line, current);
                    i++;
                }
                if (!closed) { set_error(source_line, "theorem proof is missing its closing '.' or 'QED.'"); return 0; }
            }
            program_add_theorem(program, theorem);
            continue;
        }
        if (starts_with(line, "Transparent ") || starts_with(line, "Notation ") || starts_with(line, "Import ") || starts_with(line, "Namespace ") || starts_with(line, "Define ")) {
            set_error(source_line, "this declaration belongs to the LRS-Alpha syntax, but is outside the implemented propositional checker");
            return 0;
        }
        set_error(source_line, "expected Axiom, Theorem, or Print axioms");
        return 0;
    }
    return 1;
}

static void context_add(Context *ctx, const char *name, Formula *formula) {
    reserve_array((void **)&ctx->items, &ctx->capacity, ctx->count + 1, sizeof *ctx->items);
    ctx->items[ctx->count].name = copy_s(name);
    ctx->items[ctx->count].formula = formula;
    ctx->count++;
}
static Formula *context_find(const Context *ctx, const char *name) {
    size_t i;
    for (i = ctx->count; i > 0; i--) if (strcmp(ctx->items[i - 1].name, name) == 0) return ctx->items[i - 1].formula;
    return NULL;
}
static void context_copy(Context *to, const Context *from) {
    memset(to, 0, sizeof *to);
    if (from->count) {
        to->items = (Binding *)xmalloc(from->count * sizeof *to->items);
        memcpy(to->items, from->items, from->count * sizeof *to->items);
        to->count = to->capacity = from->count;
    }
}

static Axiom *find_axiom(Program *p, const char *name) {
    size_t i;
    for (i = 0; i < p->axiom_count; i++) if (strcmp(p->axioms[i].name, name) == 0) return &p->axioms[i];
    return NULL;
}
static Theorem *find_theorem(Program *p, const char *name) {
    size_t i;
    for (i = 0; i < p->theorem_count; i++) if (strcmp(p->theorems[i].name, name) == 0) return &p->theorems[i];
    return NULL;
}
static int string_array_has(char **items, size_t count, const char *name) {
    size_t i;
    for (i = 0; i < count; i++) if (strcmp(items[i], name) == 0) return 1;
    return 0;
}
static void theorem_add_dependency(Theorem *theorem, const char *name) {
    if (string_array_has(theorem->dependencies, theorem->dependency_count, name)) return;
    reserve_array((void **)&theorem->dependencies, &theorem->dependency_capacity, theorem->dependency_count + 1, sizeof *theorem->dependencies);
    theorem->dependencies[theorem->dependency_count++] = copy_s(name);
}

static int arg_count(const ProofTerm *term, size_t count, int line) {
    if (term->argc == count) return 1;
    set_error(line, "%s expects %zu argument(s), got %zu", term->name, count, term->argc);
    return 0;
}
static ProofTerm *arg_term(const ProofTerm *term, size_t index, int line) {
    if (index >= term->argc || term->args[index].kind != ARG_TERM) {
        set_error(line, "argument to %s must be a proof term", term->name);
        return NULL;
    }
    return term->args[index].term;
}
static char *arg_name(const ProofTerm *term, size_t index, int line) {
    if (index >= term->argc || term->args[index].kind != ARG_NAME || !valid_name(term->args[index].name)) {
        set_error(line, "argument to %s must be a quoted name", term->name);
        return NULL;
    }
    return term->args[index].name;
}
static Formula *arg_formula(const ProofTerm *term, size_t index, int line) {
    if (index >= term->argc || term->args[index].kind != ARG_FORMULA) {
        set_error(line, "argument to %s must be formula(\"...\")", term->name);
        return NULL;
    }
    return term->args[index].formula;
}

static Formula *infer_proof(Program *program, Theorem *current, ProofTerm *term, Context *local, int line);

static Formula *infer_name(Program *program, Theorem *current, const char *name, Context *local, int line) {
    Formula *local_formula = context_find(local, name);
    Axiom *axiom;
    Theorem *theorem;
    size_t n = strlen(name);
    if (local_formula) return local_formula;
    axiom = find_axiom(program, name);
    if (axiom) {
        theorem_add_dependency(current, name);
        return axiom->formula;
    }
    theorem = find_theorem(program, name);
    if (theorem && theorem->checked) {
        theorem_add_dependency(current, name);
        return theorem->claim;
    }
    if (theorem && theorem->incomplete) {
        set_error(line, "'%s' is incomplete and cannot be referenced", name);
        return NULL;
    }
    if (n > 2 && (strcmp(name + n - 2, ".1") == 0 || strcmp(name + n - 2, ".2") == 0)) {
        char *pair_name = copy_n(name, n - 2);
        Formula *pair = context_find(local, pair_name);
        int first = name[n - 1] == '1';
        if (!pair) {
            Axiom *pair_axiom = find_axiom(program, pair_name);
            Theorem *pair_theorem = find_theorem(program, pair_name);
            if (pair_axiom) { pair = pair_axiom->formula; theorem_add_dependency(current, pair_name); }
            else if (pair_theorem && pair_theorem->checked) { pair = pair_theorem->claim; theorem_add_dependency(current, pair_name); }
            else if (pair_theorem && pair_theorem->incomplete) {
                set_error(line, "'%s' is incomplete and cannot be referenced", pair_name);
                return NULL;
            }
        }
        if (pair) {
            if (pair->kind != F_AND) {
                set_error(line, "projection '%s' requires a proof of P /\\ Q", name);
                return NULL;
            }
            return first ? pair->left : pair->right;
        }
    }
    set_error(line, "unknown proof name '%s'", name);
    return NULL;
}

static Formula *infer_proof(Program *program, Theorem *current, ProofTerm *term, Context *local, int line) {
    Formula *a, *b, *c;
    Context nested;
    char *name;
    ProofTerm *sub;
    if (strcmp(term->name, "$formula") == 0) {
        set_error(line, "formula(...) is only valid as an argument");
        return NULL;
    }
    if (strcmp(term->name, "imp_intro") == 0) {
        if (!arg_count(term, 3, line)) return NULL;
        name = arg_name(term, 0, line); if (!name) return NULL;
        a = arg_formula(term, 1, line); if (!a) return NULL;
        sub = arg_term(term, 2, line); if (!sub) return NULL;
        if (context_find(local, name) || find_axiom(program, name) || find_theorem(program, name)) {
            set_error(line, "local name '%s' is already in scope", name); return NULL;
        }
        context_copy(&nested, local);
        context_add(&nested, name, a);
        b = infer_proof(program, current, sub, &nested, line);
        if (!b) return NULL;
        return new_formula(F_IMP, NULL, a, b);
    }
    if (strcmp(term->name, "imp_apply") == 0) {
        if (!arg_count(term, 2, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        b = infer_proof(program, current, arg_term(term, 1, line), local, line); if (!b) return NULL;
        if (a->kind != F_IMP || !formula_equal(a->left, b)) {
            char *got = format_formula(b);
            set_error(line, "imp_apply expected a proof of %s and received %s", a->kind == F_IMP ? format_formula(a->left) : "P -> Q", got);
            return NULL;
        }
        return a->right;
    }
    if (strcmp(term->name, "and_intro") == 0) {
        if (!arg_count(term, 2, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        b = infer_proof(program, current, arg_term(term, 1, line), local, line); if (!b) return NULL;
        return new_formula(F_AND, NULL, a, b);
    }
    if (strcmp(term->name, "and_left") == 0 || strcmp(term->name, "and_right") == 0) {
        if (!arg_count(term, 1, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        if (a->kind != F_AND) { set_error(line, "%s requires a proof of P and Q, received %s", term->name, format_formula(a)); return NULL; }
        return strcmp(term->name, "and_left") == 0 ? a->left : a->right;
    }
    if (strcmp(term->name, "or_left") == 0 || strcmp(term->name, "or_right") == 0) {
        if (!arg_count(term, 2, line)) return NULL;
        if (strcmp(term->name, "or_left") == 0) {
            a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
            b = arg_formula(term, 1, line); if (!b) return NULL;
            return new_formula(F_OR, NULL, a, b);
        }
        a = arg_formula(term, 0, line); if (!a) return NULL;
        b = infer_proof(program, current, arg_term(term, 1, line), local, line); if (!b) return NULL;
        return new_formula(F_OR, NULL, a, b);
    }
    if (strcmp(term->name, "or_cases") == 0) {
        Context left_ctx, right_ctx;
        ProofTerm *left_proof, *right_proof;
        char *left_name, *right_name;
        if (!arg_count(term, 5, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        if (a->kind != F_OR) { set_error(line, "or_cases requires a proof of P or Q, received %s", format_formula(a)); return NULL; }
        left_name = arg_name(term, 1, line); if (!left_name) return NULL;
        left_proof = arg_term(term, 2, line); if (!left_proof) return NULL;
        right_name = arg_name(term, 3, line); if (!right_name) return NULL;
        right_proof = arg_term(term, 4, line); if (!right_proof) return NULL;
        if (context_find(local, left_name) || context_find(local, right_name) || find_axiom(program, left_name) || find_axiom(program, right_name) || find_theorem(program, left_name) || find_theorem(program, right_name)) {
            set_error(line, "or_cases branch names must be fresh in their scope"); return NULL;
        }
        context_copy(&left_ctx, local); context_copy(&right_ctx, local);
        context_add(&left_ctx, left_name, a->left); context_add(&right_ctx, right_name, a->right);
        b = infer_proof(program, current, left_proof, &left_ctx, line); if (!b) return NULL;
        c = infer_proof(program, current, right_proof, &right_ctx, line); if (!c) return NULL;
        if (!formula_equal(b, c)) { set_error(line, "or_cases branches disagree: %s versus %s", format_formula(b), format_formula(c)); return NULL; }
        return b;
    }
    if (strcmp(term->name, "false_elim") == 0) {
        if (!arg_count(term, 2, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        b = arg_formula(term, 1, line); if (!b) return NULL;
        if (a->kind != F_FALSE) { set_error(line, "false_elim requires a proof of False, received %s", format_formula(a)); return NULL; }
        return b;
    }
    if (strcmp(term->name, "iff_intro") == 0) {
        if (!arg_count(term, 2, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        b = infer_proof(program, current, arg_term(term, 1, line), local, line); if (!b) return NULL;
        if (a->kind != F_IMP || b->kind != F_IMP || !formula_equal(a->left, b->right) || !formula_equal(a->right, b->left)) {
            set_error(line, "iff_intro expects proofs of P -> Q and Q -> P"); return NULL;
        }
        return new_formula(F_IFF, NULL, a->left, a->right);
    }
    if (strcmp(term->name, "iff_left") == 0 || strcmp(term->name, "iff_right") == 0) {
        if (!arg_count(term, 1, line)) return NULL;
        a = infer_proof(program, current, arg_term(term, 0, line), local, line); if (!a) return NULL;
        if (a->kind != F_IFF) { set_error(line, "%s requires a proof of P <-> Q, received %s", term->name, format_formula(a)); return NULL; }
        return strcmp(term->name, "iff_left") == 0 ? new_formula(F_IMP, NULL, a->left, a->right) : new_formula(F_IMP, NULL, a->right, a->left);
    }
    if (term->argc != 0) { set_error(line, "unknown proof function '%s'", term->name); return NULL; }
    return infer_name(program, current, term->name, local, line);
}

static int find_by_marker(const char *s, const char *marker) {
    int depth = 0;
    size_t marker_len = strlen(marker);
    for (size_t i = 0; s[i]; i++) {
        if (s[i] == '(') depth++;
        else if (s[i] == ')' && depth > 0) depth--;
        if (depth == 0 && strncmp(s + i, marker, marker_len) == 0) return (int)i;
    }
    return -1;
}

static int parse_step_line(const char *sentence, char **name, char **formula_text, char **proof_text) {
    char *copy;
    char *body;
    int colon, marker;
    size_t n;
    if (!starts_with(sentence, "Step ")) return 0;
    copy = trim_copy(sentence + 5);
    colon = find_char_outside(copy, ':');
    marker = find_by_marker(copy, ", by [");
    n = strlen(copy);
    if (colon < 0 || marker < 0 || n < 2 || copy[n - 2] != ']' || copy[n - 1] != '.') return 0;
    *name = trim_copy(copy_n(copy, (size_t)colon));
    if (!valid_name(*name)) return 0;
    body = copy + colon + 1;
    if ((size_t)(body - copy) > (size_t)marker) return 0;
    *formula_text = trim_copy(copy_n(body, (size_t)(copy + marker - body)));
    *proof_text = trim_copy(copy_n(copy + marker + 6, n - (size_t)marker - 8));
    return 1;
}

static int parse_hence_line(const char *sentence, char **formula_text, char **proof_text) {
    char *copy;
    int marker;
    size_t n;
    if (!starts_with(sentence, "Hence ")) return 0;
    copy = trim_copy(sentence + 6);
    n = strlen(copy);
    if (n < 3 || copy[n - 2] != ']' || copy[n - 1] != '.') return 0;
    marker = find_by_marker(copy, " by [");
    if (marker < 0) return 0;
    *formula_text = trim_copy(copy_n(copy, (size_t)marker));
    *proof_text = trim_copy(copy_n(copy + marker + 5, n - (size_t)marker - 7));
    return 1;
}

static int check_theorems(Program *program) {
    for (size_t ti = 0; ti < program->theorem_count; ti++) {
        Theorem *theorem = &program->theorems[ti];
        Context local;
        int saw_todo = 0;
        int saw_final = 0;
        memset(&local, 0, sizeof local);
        for (size_t pi = 0; pi < theorem->proof_count; pi++) {
            ProofLine *pline = &theorem->proof[pi];
            char *sentence = pline->text;
            int line = pline->line;
            if (strcmp(sentence, "Todo.") == 0) {
                if (saw_final) { set_error(line, "Todo cannot follow the final Hence"); return 0; }
                saw_todo = 1;
                continue;
            }
            {
                char *step_name = NULL, *formula_text = NULL, *proof_text = NULL;
                if (parse_step_line(sentence, &step_name, &formula_text, &proof_text)) {
                    Formula *expected, *actual;
                    ProofTerm *proof;
                    if (saw_final) { set_error(line, "no proof sentence may follow the final Hence"); return 0; }
                    if (context_find(&local, step_name) || find_axiom(program, step_name) || find_theorem(program, step_name)) {
                        set_error(line, "duplicate or shadowing proof name '%s'", step_name); return 0;
                    }
                    expected = parse_formula(formula_text, line); if (!expected) return 0;
                    proof = parse_proof_term(proof_text, line); if (!proof) return 0;
                    actual = infer_proof(program, theorem, proof, &local, line); if (!actual) return 0;
                    if (!formula_equal(actual, expected)) {
                        set_error(line, "step '%s' claims %s, but its proof has type %s", step_name, format_formula(expected), format_formula(actual)); return 0;
                    }
                    context_add(&local, step_name, expected);
                    continue;
                }
            }
            {
                char *formula_text = NULL, *proof_text = NULL;
                if (parse_hence_line(sentence, &formula_text, &proof_text)) {
                    Formula *expected, *actual;
                    ProofTerm *proof;
                    if (saw_final) { set_error(line, "a theorem may contain only one final Hence"); return 0; }
                    expected = parse_formula(formula_text, line); if (!expected) return 0;
                    proof = parse_proof_term(proof_text, line); if (!proof) return 0;
                    actual = infer_proof(program, theorem, proof, &local, line); if (!actual) return 0;
                    if (!formula_equal(actual, expected)) {
                        set_error(line, "Hence claims %s, but its proof has type %s", format_formula(expected), format_formula(actual)); return 0;
                    }
                    if (!formula_equal(expected, theorem->claim)) {
                        set_error(line, "final Hence proves %s, but theorem claim is %s", format_formula(expected), format_formula(theorem->claim)); return 0;
                    }
                    saw_final = 1;
                    continue;
                }
            }
            if (saw_final) { set_error(line, "no proof sentence may follow the final proof term"); return 0; }
            {
                ProofTerm *proof = parse_proof_term(sentence, line);
                Formula *actual;
                if (!proof) return 0;
                actual = infer_proof(program, theorem, proof, &local, line); if (!actual) return 0;
                if (!formula_equal(actual, theorem->claim)) {
                    set_error(line, "proof term has type %s, but theorem claim is %s", format_formula(actual), format_formula(theorem->claim)); return 0;
                }
                saw_final = 1;
            }
        }
        if (saw_todo) {
            theorem->incomplete = 1;
            continue;
        }
        if (!saw_final) { set_error(theorem->line, "completed theorem needs one final proof; use Todo. for an unfinished theorem"); return 0; }
        theorem->checked = 1;
    }
    return 1;
}

static int compare_names(const void *a, const void *b) {
    const char *const *aa = (const char *const *)a;
    const char *const *bb = (const char *const *)b;
    return strcmp(*aa, *bb);
}

static void visit_dependencies(Program *program, const char *name, char ***seen, size_t *seen_count, size_t *seen_capacity, char ***axioms, size_t *axiom_count, size_t *axiom_capacity) {
    Axiom *axiom;
    Theorem *theorem;
    if (string_array_has(*seen, *seen_count, name)) return;
    reserve_array((void **)seen, seen_capacity, *seen_count + 1, sizeof **seen);
    (*seen)[(*seen_count)++] = copy_s(name);
    axiom = find_axiom(program, name);
    if (axiom) {
        if (!string_array_has(*axioms, *axiom_count, name)) {
            reserve_array((void **)axioms, axiom_capacity, *axiom_count + 1, sizeof **axioms);
            (*axioms)[(*axiom_count)++] = copy_s(name);
        }
        return;
    }
    theorem = find_theorem(program, name);
    if (!theorem) return;
    for (size_t i = 0; i < theorem->dependency_count; i++)
        visit_dependencies(program, theorem->dependencies[i], seen, seen_count, seen_capacity, axioms, axiom_count, axiom_capacity);
}

static int print_axiom_reports(Program *program) {
    for (size_t pi = 0; pi < program->print_count; pi++) {
        PrintRequest *request = &program->prints[pi];
        char **seen = NULL, **axioms = NULL, **unfinished = NULL;
        size_t seen_count = 0, seen_capacity = 0, axiom_count = 0, axiom_capacity = 0;
        size_t unfinished_count = 0, unfinished_capacity = 0;
        if (!find_axiom(program, request->name) && !find_theorem(program, request->name)) {
            set_error(request->line, "unknown theorem or axiom '%s'", request->name);
            return 0;
        }
        visit_dependencies(program, request->name, &seen, &seen_count, &seen_capacity, &axioms, &axiom_count, &axiom_capacity);
        for (size_t i = 0; i < seen_count; i++) {
            Theorem *t = find_theorem(program, seen[i]);
            if (t && t->incomplete) {
                reserve_array((void **)&unfinished, &unfinished_capacity, unfinished_count + 1, sizeof *unfinished);
                unfinished[unfinished_count++] = copy_s(t->name);
            }
        }
        if (axiom_count > 1) qsort(axioms, axiom_count, sizeof *axioms, compare_names);
        if (unfinished_count > 1) qsort(unfinished, unfinished_count, sizeof *unfinished, compare_names);
        printf("%s: axioms = ", request->name);
        if (!axiom_count) printf("none");
        for (size_t i = 0; i < axiom_count; i++) printf("%s%s", i ? ", " : "", axioms[i]);
        printf("; unfinished = ");
        if (!unfinished_count) printf("none");
        for (size_t i = 0; i < unfinished_count; i++) printf("%s%s", i ? ", " : "", unfinished[i]);
        putchar('\n');
    }
    return 1;
}

static int validate_print_requests(Program *program) {
    for (size_t i = 0; i < program->print_count; i++) {
        PrintRequest *request = &program->prints[i];
        if (!find_axiom(program, request->name) && !find_theorem(program, request->name)) {
            set_error(request->line, "unknown theorem or axiom '%s'", request->name);
            return 0;
        }
    }
    return 1;
}

static char *read_all(FILE *file) {
    StringBuilder sb;
    int c;
    sb_init(&sb);
    while ((c = fgetc(file)) != EOF) {
        char ch = (char)c;
        sb_append_n(&sb, &ch, 1);
    }
    if (ferror(file)) return NULL;
    if (!sb.data) return copy_s("");
    if (sb.length >= 3 && (unsigned char)sb.data[0] == 0xEF && (unsigned char)sb.data[1] == 0xBB && (unsigned char)sb.data[2] == 0xBF) {
        memmove(sb.data, sb.data + 3, sb.length - 2);
        sb.length -= 3;
    }
    return sb.data;
}

static int run_check(const char *path) {
    FILE *file = fopen(path, "rb");
    char *source;
    Program program;
    if (!file) {
        fprintf(stderr, "lloyd: %s: %s\n", path, strerror(errno));
        return 2;
    }
    source = read_all(file);
    if (fclose(file) != 0 && !source) source = NULL;
    if (!source) {
        fprintf(stderr, "lloyd: failed to read %s\n", path);
        return 2;
    }
    memset(&program, 0, sizeof program);
    g_error[0] = '\0';
    g_error_line = 0;
    if (!parse_source(&program, source) || !check_theorems(&program) || !validate_print_requests(&program)) {
        if (g_error_line) fprintf(stderr, "lloyd: line %d: %s\n", g_error_line, g_error);
        else fprintf(stderr, "lloyd: %s\n", g_error[0] ? g_error : "invalid source");
        return 1;
    }
    for (size_t i = 0; i < program.theorem_count; i++) {
        Theorem *t = &program.theorems[i];
        if (t->checked) printf("checked: %s: %s\n", t->name, format_formula(t->claim));
        else if (t->incomplete) printf("incomplete: %s\n", t->name);
    }
    if (!print_axiom_reports(&program)) {
        if (g_error_line) fprintf(stderr, "lloyd: line %d: %s\n", g_error_line, g_error);
        else fprintf(stderr, "lloyd: %s\n", g_error[0] ? g_error : "invalid source");
        return 1;
    }
    {
        int any_incomplete = 0;
        for (size_t i = 0; i < program.theorem_count; i++) if (program.theorems[i].incomplete) any_incomplete = 1;
        if (any_incomplete) {
            puts("file is not certified because it contains unfinished theorems");
            return 1;
        }
    }
    puts("file certified for the supported propositional fragment");
    return 0;
}

static void usage(FILE *out) {
    fputs("Usage: lloyd check <file.lloyd>\n", out);
    fputs("Check the explicit intuitionistic propositional fragment of Lloyd LRS-Alpha.\n", out);
}

int main(int argc, char **argv) {
    if (argc == 2 && (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0)) {
        usage(stdout);
        return 0;
    }
    if (argc == 3 && strcmp(argv[1], "check") == 0) return run_check(argv[2]);
    usage(stderr);
    return 2;
}
