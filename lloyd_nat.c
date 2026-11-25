/*
 * LRS-Alpha Nat/equality proof checker extension.
 * Included by lloyd.c so the Windows build remains a single compiler command.
 * This module accepts the explicitly implemented grammar subset documented
 * in README.md; it is not a parser for every construct in the LRS-Alpha draft.
 *BSD 3-Clause License
 *Copyright (c) 2026, 九七のねこ
 */
typedef enum { X_ZERO, X_VAR, X_SUCC, X_ADD, X_LAMBDA } XTermKind;
typedef struct XTerm XTerm;
struct XTerm {
    XTermKind kind;
    char *name;
    XTerm *a;
    XTerm *b;
};
typedef struct { XTerm *left; XTerm *right; } XEq;

typedef enum { XT_ID, XT_NUM, XT_LP, XT_RP, XT_PLUS, XT_EQ, XT_ARROW, XT_COMMA, XT_COLON, XT_DOT, XT_LB, XT_RB } XTokKind;
typedef struct { XTokKind kind; char *text; int line; } XTok;
typedef struct { XTok *items; size_t count; size_t capacity; size_t pos; int line; } XParser;
typedef struct { char *name; XEq value; } XFact;
typedef struct { XFact *items; size_t count; size_t capacity; } XFacts;
typedef enum { XP_REF, XP_SYMM, XP_TRANS, XP_REFL, XP_CONGR, XP_BUILTIN } XProofKind;
typedef struct XProof XProof;
struct XProof {
    XProofKind kind;
    char *name;
    XProof *first;
    XProof *second;
    XTerm *term;
    XTerm *arg1;
    XTerm *arg2;
};
typedef struct { char *text; int indent; int line; } XLine;
typedef struct {
    char *name;
    XEq claim;
    char **lets;
    size_t let_count;
    char *induction_var;
    XLine case_headers[2];
    XLine *case_lines[2];
    size_t case_counts[2];
    size_t case_caps[2];
    size_t case_count;
    int line;
} XTheorem;

static void x_set_error(int line, const char *fmt, ...) {
    va_list args;
    if (g_error[0]) return;
    g_error_line = line;
    va_start(args, fmt);
    vsnprintf(g_error, sizeof g_error, fmt, args);
    va_end(args);
}

static XTerm *x_term(XTermKind kind, const char *name, XTerm *a, XTerm *b) {
    XTerm *t = (XTerm *)xmalloc(sizeof *t);
    t->kind = kind;
    t->name = name ? copy_s(name) : NULL;
    t->a = a;
    t->b = b;
    return t;
}

static int x_term_equal(const XTerm *a, const XTerm *b) {
    if (a == b) return 1;
    if (!a || !b || a->kind != b->kind) return 0;
    if (a->kind == X_VAR) return strcmp(a->name, b->name) == 0;
    if (a->kind == X_ZERO) return 1;
    if (a->kind == X_LAMBDA && strcmp(a->name, b->name) != 0) return 0;
    return x_term_equal(a->a, b->a) && x_term_equal(a->b, b->b);
}

static XTerm *x_substitute(const XTerm *term, const char *name, const XTerm *value) {
    if (term->kind == X_VAR) return strcmp(term->name, name) == 0 ? (XTerm *)value : x_term(X_VAR, term->name, NULL, NULL);
    if (term->kind == X_ZERO) return x_term(X_ZERO, NULL, NULL, NULL);
    if (term->kind == X_LAMBDA && strcmp(term->name, name) == 0)
        return x_term(X_LAMBDA, term->name, (XTerm *)term->a, NULL);
    if (term->kind == X_LAMBDA)
        return x_term(X_LAMBDA, term->name, x_substitute(term->a, name, value), NULL);
    return x_term(term->kind, NULL, x_substitute(term->a, name, value), term->b ? x_substitute(term->b, name, value) : NULL);
}

static void x_format_term_into(StringBuilder *sb, const XTerm *term, int parent_precedence) {
    int precedence = term->kind == X_ADD ? 1 : 2;
    if (precedence < parent_precedence) sb_append(sb, "(");
    switch (term->kind) {
        case X_ZERO: sb_append(sb, "Nat.zero"); break;
        case X_VAR: sb_append(sb, term->name); break;
        case X_SUCC:
            sb_append(sb, "Nat.succ ");
            if (term->a->kind == X_ADD) {
                sb_append(sb, "("); x_format_term_into(sb, term->a, 0); sb_append(sb, ")");
            } else x_format_term_into(sb, term->a, precedence);
            break;
        case X_ADD:
            x_format_term_into(sb, term->a, precedence);
            sb_append(sb, " + ");
            x_format_term_into(sb, term->b, precedence + 1);
            break;
        case X_LAMBDA:
            sb_append(sb, "fun "); sb_append(sb, term->name); sb_append(sb, " => ");
            x_format_term_into(sb, term->a, 0);
            break;
    }
    if (precedence < parent_precedence) sb_append(sb, ")");
}

static char *x_format_term(const XTerm *term) {
    StringBuilder sb; sb_init(&sb); x_format_term_into(&sb, term, 0); return sb.data ? sb.data : copy_s("");
}

static int x_eq_equal(XEq a, XEq b) { return x_term_equal(a.left, b.left) && x_term_equal(a.right, b.right); }
static char *x_format_eq(XEq eq) {
    StringBuilder sb; sb_init(&sb); x_format_term_into(&sb, eq.left, 0); sb_append(&sb, " = "); x_format_term_into(&sb, eq.right, 0); return sb.data ? sb.data : copy_s("");
}

static XTok *x_peek(XParser *p) { return p->pos < p->count ? &p->items[p->pos] : NULL; }
static int x_accept(XParser *p, XTokKind kind) { if (p->pos < p->count && p->items[p->pos].kind == kind) { p->pos++; return 1; } return 0; }

static int x_lex(XParser *p, const char *text, int line) {
    size_t i = 0;
    memset(p, 0, sizeof *p);
    p->line = line;
    while (text[i]) {
        unsigned char c = (unsigned char)text[i];
        XTok tok; memset(&tok, 0, sizeof tok); tok.line = line;
        if (isspace(c)) { i++; continue; }
        if (is_ident_start(c)) {
            size_t start = i++;
            while (is_ident_part((unsigned char)text[i])) {
                if (text[i] == '.' && !is_ident_start((unsigned char)text[i + 1])) break;
                i++;
            }
            tok.kind = XT_ID; tok.text = copy_n(text + start, i - start);
        } else if (isdigit(c)) {
            size_t start = i++;
            while (isdigit((unsigned char)text[i])) i++;
            tok.kind = XT_NUM; tok.text = copy_n(text + start, i - start);
        } else if (text[i] == '=' && text[i + 1] == '>') { tok.kind = XT_ARROW; tok.text = copy_s("=>"); i += 2; }
        else {
            tok.text = copy_n(text + i, 1);
            switch (text[i]) {
                case '(': tok.kind = XT_LP; break;
                case ')': tok.kind = XT_RP; break;
                case '+': tok.kind = XT_PLUS; break;
                case '=': tok.kind = XT_EQ; break;
                case ',': tok.kind = XT_COMMA; break;
                case ':': tok.kind = XT_COLON; break;
                case '.': tok.kind = XT_DOT; break;
                case '[': tok.kind = XT_LB; break;
                case ']': tok.kind = XT_RB; break;
                default: x_set_error(line, "unsupported character '%c' in Nat/equality syntax", text[i]); return 0;
            }
            i++;
        }
        reserve_array((void **)&p->items, &p->capacity, p->count + 1, sizeof *p->items);
        p->items[p->count++] = tok;
    }
    return 1;
}

static XTerm *x_parse_term(XParser *p);

static XTerm *x_parse_atom(XParser *p) {
    XTok *tok = x_peek(p);
    if (!tok) { x_set_error(p->line, "expected a Nat term"); return NULL; }
    if (x_accept(p, XT_LP)) {
        XTerm *inner;
        if (x_peek(p) && x_peek(p)->kind == XT_ID && strcmp(x_peek(p)->text, "fun") == 0) {
            char *binder; XTerm *body;
            p->pos++;
            tok = x_peek(p);
            if (!tok || tok->kind != XT_ID) { x_set_error(p->line, "expected lambda binder after 'fun'"); return NULL; }
            binder = tok->text; p->pos++;
            if (!x_accept(p, XT_ARROW)) { x_set_error(p->line, "expected '=>' in lambda"); return NULL; }
            body = x_parse_term(p); if (!body) return NULL;
            if (!x_accept(p, XT_RP)) { x_set_error(p->line, "expected ')' after lambda"); return NULL; }
            return x_term(X_LAMBDA, binder, body, NULL);
        }
        inner = x_parse_term(p); if (!inner) return NULL;
        if (!x_accept(p, XT_RP)) { x_set_error(p->line, "expected ')' in Nat term"); return NULL; }
        return inner;
    }
    if (tok->kind == XT_ID && strcmp(tok->text, "fun") == 0) {
        char *binder; XTerm *body;
        p->pos++;
        tok = x_peek(p);
        if (!tok || tok->kind != XT_ID) { x_set_error(p->line, "expected lambda binder after 'fun'"); return NULL; }
        binder = tok->text; p->pos++;
        if (!x_accept(p, XT_ARROW)) { x_set_error(p->line, "expected '=>' in lambda"); return NULL; }
        body = x_parse_term(p); if (!body) return NULL;
        return x_term(X_LAMBDA, binder, body, NULL);
    }
    if (tok->kind == XT_NUM) {
        unsigned long value = strtoul(tok->text, NULL, 10);
        XTerm *result = x_term(X_ZERO, NULL, NULL, NULL);
        p->pos++;
        if (value > 10000UL) { x_set_error(p->line, "Nat numeral is too large"); return NULL; }
        while (value--) result = x_term(X_SUCC, NULL, result, NULL);
        return result;
    }
    if (tok->kind == XT_ID) {
        char *name = tok->text;
        p->pos++;
        if (strcmp(name, "Nat.zero") == 0) return x_term(X_ZERO, NULL, NULL, NULL);
        if (strcmp(name, "Nat.succ") == 0) {
            XTerm *arg = x_parse_atom(p);
            if (!arg) { x_set_error(p->line, "Nat.succ expects one Nat argument"); return NULL; }
            return x_term(X_SUCC, NULL, arg, NULL);
        }
        if (strchr(name, '.')) { x_set_error(p->line, "unknown Nat constant '%s'", name); return NULL; }
        return x_term(X_VAR, name, NULL, NULL);
    }
    x_set_error(p->line, "expected a Nat term");
    return NULL;
}

static XTerm *x_parse_term(XParser *p) {
    XTerm *left = x_parse_atom(p);
    if (!left) return NULL;
    while (x_accept(p, XT_PLUS)) {
        XTerm *right = x_parse_atom(p);
        if (!right) return NULL;
        left = x_term(X_ADD, NULL, left, right);
    }
    return left;
}

static int x_find_equal(const char *text) {
    int depth = 0;
    for (int i = 0; text[i]; i++) {
        if (text[i] == '(') depth++;
        else if (text[i] == ')' && depth > 0) depth--;
        else if (text[i] == '=' && depth == 0 && text[i + 1] != '>') return i;
    }
    return -1;
}

static XEq x_parse_eq(const char *text, int line, int *ok) {
    XEq result; memset(&result, 0, sizeof result); *ok = 0;
    int equal = x_find_equal(text);
    if (equal < 0) { x_set_error(line, "expected an equality proposition with '='"); return result; }
    char *left_text = trim_copy(copy_n(text, (size_t)equal));
    char *right_text = trim_copy(text + equal + 1);
    XParser lp, rp;
    if (!x_lex(&lp, left_text, line) || !x_lex(&rp, right_text, line)) return result;
    result.left = x_parse_term(&lp); if (!result.left) return result;
    result.right = x_parse_term(&rp); if (!result.right) return result;
    if (lp.pos != lp.count || rp.pos != rp.count) { x_set_error(line, "unexpected token in equality proposition"); return result; }
    *ok = 1; return result;
}

static XTerm *x_subst_eq_side(const XTerm *term, const char *name, const XTerm *value) { return x_substitute(term, name, value); }
static XEq x_substitute_eq(XEq eq, const char *name, const XTerm *value) {
    XEq out; out.left = x_subst_eq_side(eq.left, name, value); out.right = x_subst_eq_side(eq.right, name, value); return out;
}

static void x_facts_add(XFacts *facts, const char *name, XEq value) {
    reserve_array((void **)&facts->items, &facts->capacity, facts->count + 1, sizeof *facts->items);
    facts->items[facts->count].name = copy_s(name); facts->items[facts->count].value = value; facts->count++;
}
static int x_fact_find(const XFacts *facts, const char *name, XEq *value) {
    for (size_t i = facts->count; i > 0; i--) if (strcmp(facts->items[i - 1].name, name) == 0) { *value = facts->items[i - 1].value; return 1; }
    return 0;
}

static int x_name_in_scope(const char *name, char **scope, size_t scope_count, const char *extra) {
    if (extra && strcmp(name, extra) == 0) return 1;
    for (size_t i = 0; i < scope_count; i++) if (strcmp(name, scope[i]) == 0) return 1;
    return 0;
}

static int x_term_scoped(const XTerm *term, char **scope, size_t scope_count, const char *extra) {
    if (!term) return 1;
    if (term->kind == X_VAR) return x_name_in_scope(term->name, scope, scope_count, extra);
    if (term->kind == X_ZERO) return 1;
    if (term->kind == X_LAMBDA) return x_term_scoped(term->a, scope, scope_count, term->name);
    return x_term_scoped(term->a, scope, scope_count, extra) && x_term_scoped(term->b, scope, scope_count, extra);
}

static int x_eq_scoped(XEq eq, char **scope, size_t scope_count) {
    return x_term_scoped(eq.left, scope, scope_count, NULL) && x_term_scoped(eq.right, scope, scope_count, NULL);
}

static XProof *x_proof(XProofKind kind) { XProof *p = (XProof *)xmalloc(sizeof *p); memset(p, 0, sizeof *p); p->kind = kind; return p; }

static void x_skip_space(const char **s) { while (**s && isspace((unsigned char)**s)) (*s)++; }
static char *x_read_name(const char **s) {
    const char *start = *s;
    if (!is_ident_start((unsigned char)**s)) return NULL;
    (*s)++;
    while (is_ident_part((unsigned char)**s)) {
        if (**s == '.' && !is_ident_start((unsigned char)(*s)[1])) break;
        (*s)++;
    }
    return copy_n(start, (size_t)(*s - start));
}

static XTerm *x_parse_term_from(const char **s, int line, int atom_only) {
    char *tail = copy_s(*s);
    XParser parser; XTerm *term;
    if (!x_lex(&parser, tail, line)) return NULL;
    term = atom_only ? x_parse_atom(&parser) : x_parse_term(&parser);
    if (!term) return NULL;
    /* The caller can parse a following proof/name after this term. */
    size_t consumed = parser.pos ? (size_t)(parser.items[parser.pos - 1].text ? strlen(parser.items[parser.pos - 1].text) : 1) : 0;
    (void)consumed;
    /* Token positions are reconstructed by scanning the consumed token spellings. */
    size_t offset = 0;
    for (size_t i = 0; i < parser.pos; i++) {
        while ((*s)[offset] && isspace((unsigned char)(*s)[offset])) offset++;
        if (parser.items[i].text) offset += strlen(parser.items[i].text);
        else offset++;
    }
    while ((*s)[offset] && isspace((unsigned char)(*s)[offset])) offset++;
    *s += offset;
    return term;
}

static XProof *x_parse_proof(const char **s, int line, int depth);

static XProof *x_parse_proof_atom(const char **s, int line, int depth) {
    x_skip_space(s);
    if (**s == '(') {
        (*s)++;
        XProof *p = x_parse_proof(s, line, depth + 1);
        x_skip_space(s);
        if (**s != ')') { x_set_error(line, "expected ')' in proof term"); return NULL; }
        (*s)++;
        return p;
    }
    return x_parse_proof(s, line, depth + 1);
}

static XProof *x_parse_proof(const char **s, int line, int depth) {
    char *name;
    XProof *p;
    if (depth > 64) { x_set_error(line, "proof term nesting limit exceeded"); return NULL; }
    x_skip_space(s);
    name = x_read_name(s);
    if (!name) { x_set_error(line, "expected proof term"); return NULL; }
    if (strcmp(name, "symm") == 0) {
        p = x_proof(XP_SYMM); p->first = x_parse_proof_atom(s, line, depth); return p->first ? p : NULL;
    }
    if (strcmp(name, "trans") == 0) {
        p = x_proof(XP_TRANS);
        p->first = x_parse_proof_atom(s, line, depth);
        p->second = x_parse_proof_atom(s, line, depth);
        return p->first && p->second ? p : NULL;
    }
    if (strcmp(name, "refl") == 0) {
        p = x_proof(XP_REFL); p->term = x_parse_term_from(s, line, 0); return p->term ? p : NULL;
    }
    if (strcmp(name, "congr") == 0) {
        p = x_proof(XP_CONGR);
        x_skip_space(s);
        p->term = x_parse_term_from(s, line, 1);
        p->first = x_parse_proof_atom(s, line, depth);
        return p->term && p->first ? p : NULL;
    }
    if (strcmp(name, "Nat.zero_add") == 0 || strcmp(name, "Nat.add_zero") == 0) {
        p = x_proof(XP_BUILTIN); p->name = name; p->arg1 = x_parse_term_from(s, line, 1); return p->arg1 ? p : NULL;
    }
    if (strcmp(name, "Nat.succ_add") == 0 || strcmp(name, "Nat.add_succ") == 0) {
        p = x_proof(XP_BUILTIN); p->name = name;
        p->arg1 = x_parse_term_from(s, line, 1);
        p->arg2 = x_parse_term_from(s, line, 1);
        return p->arg1 && p->arg2 ? p : NULL;
    }
    p = x_proof(XP_REF); p->name = name; return p;
}

static XTerm *x_apply_fun(const XTerm *fn, const XTerm *arg, int line) {
    if (!fn || fn->kind != X_LAMBDA) { x_set_error(line, "congr expects a function lambda"); return NULL; }
    return x_substitute(fn->a, fn->name, arg);
}

static XEq x_infer_proof(const XProof *proof, XFacts *facts, int line, int *ok) {
    XEq none; memset(&none, 0, sizeof none); *ok = 0;
    if (!proof) return none;
    if (proof->kind == XP_REF) {
        if (x_fact_find(facts, proof->name, &none)) { *ok = 1; return none; }
        x_set_error(line, "unknown equality proof '%s'", proof->name); return none;
    }
    if (proof->kind == XP_BUILTIN) {
        XEq e;
        if (strcmp(proof->name, "Nat.zero_add") == 0) {
            e.left = x_term(X_ADD, NULL, x_term(X_ZERO, NULL, NULL, NULL), proof->arg1); e.right = proof->arg1;
        } else if (strcmp(proof->name, "Nat.add_zero") == 0) {
            e.left = x_term(X_ADD, NULL, proof->arg1, x_term(X_ZERO, NULL, NULL, NULL)); e.right = proof->arg1;
        } else if (strcmp(proof->name, "Nat.succ_add") == 0) {
            e.left = x_term(X_ADD, NULL, x_term(X_SUCC, NULL, proof->arg1, NULL), proof->arg2);
            e.right = x_term(X_SUCC, NULL, x_term(X_ADD, NULL, proof->arg1, proof->arg2), NULL);
        } else {
            e.left = x_term(X_ADD, NULL, proof->arg1, x_term(X_SUCC, NULL, proof->arg2, NULL));
            e.right = x_term(X_SUCC, NULL, x_term(X_ADD, NULL, proof->arg1, proof->arg2), NULL);
        }
        *ok = 1; return e;
    }
    if (proof->kind == XP_REFL) { none.left = proof->term; none.right = proof->term; *ok = 1; return none; }
    if (proof->kind == XP_SYMM) {
        XEq e = x_infer_proof(proof->first, facts, line, ok);
        if (*ok) { XTerm *tmp = e.left; e.left = e.right; e.right = tmp; }
        return e;
    }
    if (proof->kind == XP_TRANS) {
        int ok1, ok2; XEq a = x_infer_proof(proof->first, facts, line, &ok1); if (!ok1) return none;
        XEq b = x_infer_proof(proof->second, facts, line, &ok2); if (!ok2) return none;
        if (!x_term_equal(a.right, b.left)) { x_set_error(line, "trans endpoints do not match: %s versus %s", x_format_term(a.right), x_format_term(b.left)); return none; }
        none.left = a.left; none.right = b.right; *ok = 1; return none;
    }
    if (proof->kind == XP_CONGR) {
        int ok1; XEq a = x_infer_proof(proof->first, facts, line, &ok1); if (!ok1) return none;
        none.left = x_apply_fun(proof->term, a.left, line); if (!none.left) return none;
        none.right = x_apply_fun(proof->term, a.right, line); if (!none.right) return none;
        *ok = 1; return none;
    }
    x_set_error(line, "unsupported equality proof rule"); return none;
}

static int x_proof_scoped(const XProof *proof, char **scope, size_t scope_count) {
    if (!proof) return 0;
    if (proof->kind == XP_REFL) return x_term_scoped(proof->term, scope, scope_count, NULL);
    if (proof->kind == XP_BUILTIN)
        return x_term_scoped(proof->arg1, scope, scope_count, NULL) && x_term_scoped(proof->arg2, scope, scope_count, NULL);
    if (proof->kind == XP_CONGR)
        return x_term_scoped(proof->term, scope, scope_count, NULL) && x_proof_scoped(proof->first, scope, scope_count);
    if (proof->kind == XP_SYMM) return x_proof_scoped(proof->first, scope, scope_count);
    if (proof->kind == XP_TRANS)
        return x_proof_scoped(proof->first, scope, scope_count) && x_proof_scoped(proof->second, scope, scope_count);
    return 1;
}

static int x_find_phrase(const char *s, const char *phrase) {
    int depth = 0; size_t n = strlen(phrase);
    for (size_t i = 0; s[i]; i++) {
        if (s[i] == '(') depth++; else if (s[i] == ')' && depth) depth--;
        if (!depth && strncmp(s + i, phrase, n) == 0) return (int)i;
    }
    return -1;
}

static int x_parse_step(const XLine *line, XFacts *facts, int final, XEq expected,
                        char **scope, size_t scope_count, int *is_hence) {
    char *text = trim_copy(line->text);
    char *name = NULL, *formula_text = NULL, *proof_text = NULL;
    int marker, ok;
    size_t n = strlen(text);
    *is_hence = 0;
    if (starts_with(text, "Step ")) {
        int colon = find_char_outside(text + 5, ':');
        marker = x_find_phrase(text, ", by [");
        if (colon < 0 || marker < 0 || n < 2 || text[n - 2] != ']' || text[n - 1] != '.') { x_set_error(line->line, "malformed Step; expected 'Step name: equality, by [proof].'"); return 0; }
        name = trim_copy(copy_n(text + 5, (size_t)colon));
        if (!valid_name(name)) { x_set_error(line->line, "invalid Step name"); return 0; }
        formula_text = trim_copy(copy_n(text + 5 + colon + 1, (size_t)(text + marker - (text + 5 + colon + 1))));
        proof_text = trim_copy(copy_n(text + marker + 6, n - (size_t)marker - 8));
    } else if (starts_with(text, "Hence ")) {
        marker = x_find_phrase(text, " by [");
        if (marker < 0 || n < 2 || text[n - 2] != ']' || text[n - 1] != '.') { x_set_error(line->line, "malformed Hence; expected 'Hence equality by [proof].'"); return 0; }
        formula_text = trim_copy(copy_n(text + 6, (size_t)(text + marker - (text + 6))));
        proof_text = trim_copy(copy_n(text + marker + 5, n - (size_t)marker - 7));
        *is_hence = 1;
    } else { x_set_error(line->line, "expected Step or final Hence in case body"); return 0; }
    int formula_ok;
    XEq claimed = x_parse_eq(formula_text, line->line, &formula_ok);
    if (!formula_ok) return 0;
    if (!x_eq_scoped(claimed, scope, scope_count)) { x_set_error(line->line, "equality refers to a Nat variable outside its scope"); return 0; }
    const char *pp = proof_text;
    XProof *proof = x_parse_proof(&pp, line->line, 0);
    if (!proof) return 0;
    x_skip_space(&pp);
    if (*pp) { x_set_error(line->line, "unexpected text after proof term: '%s'", pp); return 0; }
    if (!x_proof_scoped(proof, scope, scope_count)) { x_set_error(line->line, "proof term refers to a Nat variable outside its scope"); return 0; }
    XEq actual = x_infer_proof(proof, facts, line->line, &ok);
    if (!ok) return 0;
    if (!x_eq_equal(actual, claimed)) { x_set_error(line->line, "proof gives %s, but line claims %s", x_format_eq(actual), x_format_eq(claimed)); return 0; }
    if (*is_hence) {
        if (!final) { x_set_error(line->line, "Hence is only valid as the last item in a case"); return 0; }
        if (!x_eq_equal(claimed, expected)) { x_set_error(line->line, "case concludes %s, but induction goal is %s", x_format_eq(claimed), x_format_eq(expected)); return 0; }
    } else {
        if (final) { x_set_error(line->line, "expected final Hence, got Step"); return 0; }
        if (x_name_in_scope(name, scope, scope_count, NULL)) { x_set_error(line->line, "Step name '%s' conflicts with a Nat variable", name); return 0; }
        if (x_fact_find(facts, name, &actual)) { x_set_error(line->line, "duplicate proof name '%s'", name); return 0; }
        x_facts_add(facts, name, claimed);
    }
    return 1;
}

static int x_parse_lines(const char *source, XLine **out, size_t *count) {
    const char *p = source, *start = source; size_t capacity = 0; int number = 1;
    *out = NULL; *count = 0;
    while (1) {
        if (*p == '\n' || *p == '\0') {
            char *raw = copy_n(start, (size_t)(p - start)); size_t n = strlen(raw); int indent = 0;
            if (n && raw[n - 1] == '\r') raw[n - 1] = '\0';
            while (raw[indent] == ' ') indent++;
            if (raw[indent] == '\t') { x_set_error(number, "tabs are not allowed for indentation"); return 0; }
            for (int i = 0; i < indent; i++) if (raw[i] == '\t') { x_set_error(number, "tabs are not allowed for indentation"); return 0; }
            if (indent % 2) { x_set_error(number, "indentation must use pairs of ASCII spaces"); return 0; }
            XLine item; item.text = trim_copy(raw + indent); item.indent = indent; item.line = number++;
            reserve_array((void **)out, &capacity, *count + 1, sizeof **out); (*out)[(*count)++] = item;
            if (!*p) break;
            start = p + 1;
        }
        p++;
    }
    return 1;
}

static int x_parse_case_header(XLine header, char **kind, char **pattern_var, char **ih_name, XEq *ih, int *has_ih) {
    char *body = trim_copy(header.text + 5); size_t n = strlen(body); *has_ih = 0;
    if (n && body[n - 1] == '.') body[n - 1] = '\0';
    char *ih_phrase = strstr(body, ", with hypothesis ");
    if (ih_phrase) {
        *ih_phrase = '\0'; ih_phrase += strlen(", with hypothesis ");
        int colon = find_char_outside(ih_phrase, ':');
        if (colon < 0) { x_set_error(header.line, "malformed induction hypothesis"); return 0; }
        *ih_name = trim_copy(copy_n(ih_phrase, (size_t)colon));
        int ok; *ih = x_parse_eq(trim_copy(ih_phrase + colon + 1), header.line, &ok); if (!ok) return 0;
        if (!valid_name(*ih_name)) { x_set_error(header.line, "invalid induction hypothesis name"); return 0; }
        *has_ih = 1;
    }
    int equal = x_find_equal(body);
    if (equal < 0) { x_set_error(header.line, "case must have the form 'Case variable = Nat.constructor.'"); return 0; }
    *kind = trim_copy(copy_n(body, (size_t)equal));
    *pattern_var = trim_copy(body + equal + 1);
    if (!valid_name(*kind)) { x_set_error(header.line, "invalid induction variable in Case"); return 0; }
    return 1;
}

static int x_parse_preamble_line(const XLine *line, int *transparent, int *notation) {
    if (starts_with(line->text, "Transparent ")) {
        if (strcmp(line->text, "Transparent Nat.add.") != 0) { x_set_error(line->line, "this implementation supports only 'Transparent Nat.add.'"); return 0; }
        *transparent = 1; return 1;
    }
    if (starts_with(line->text, "Notation ")) {
        if (strcmp(line->text, "Notation \"+\" on Nat precedence 60 left := Nat.add.") != 0) {
            x_set_error(line->line, "expected 'Notation \"+\" on Nat precedence 60 left := Nat.add.'"); return 0;
        }
        if (!*transparent) { x_set_error(line->line, "Notation must follow the Transparent Nat.add declaration"); return 0; }
        *notation = 1; return 1;
    }
    return 0;
}

static int x_check_case(XTheorem *theorem, size_t branch, XTerm *substitution, const char *case_var,
                        int successor_case, char *ih_name, XEq ih_eq, int has_ih, int transparent, int notation) {
    XLine header = theorem->case_headers[branch];
    XEq target = x_substitute_eq(theorem->claim, theorem->induction_var, substitution);
    XFacts facts; memset(&facts, 0, sizeof facts);
    char **scope = (char **)xmalloc((theorem->let_count + 1) * sizeof *scope);
    size_t scope_count = 0;
    for (size_t i = 0; i < theorem->let_count; i++) {
        if (strcmp(theorem->lets[i], theorem->induction_var) != 0) scope[scope_count++] = theorem->lets[i];
    }
    if (successor_case) scope[scope_count++] = (char *)case_var;
    if (!x_eq_scoped(target, scope, scope_count)) { x_set_error(header.line, "induction goal contains an out-of-scope variable"); return 0; }
    if (!transparent || !notation) { x_set_error(header.line, "Nat addition proof requires Transparent Nat.add and its '+' notation"); return 0; }
    if (successor_case) {
        XEq expected_ih = x_substitute_eq(theorem->claim, theorem->induction_var, x_term(X_VAR, case_var, NULL, NULL));
        if (!has_ih || !x_eq_equal(ih_eq, expected_ih)) { x_set_error(header.line, "induction hypothesis does not match the theorem motive"); return 0; }
        if (!x_eq_scoped(ih_eq, scope, scope_count)) { x_set_error(header.line, "induction hypothesis contains an out-of-scope variable"); return 0; }
        if (x_name_in_scope(ih_name, scope, scope_count, NULL)) { x_set_error(header.line, "induction hypothesis name conflicts with a Nat variable"); return 0; }
        x_facts_add(&facts, ih_name, ih_eq);
    } else if (has_ih) { x_set_error(header.line, "base case must not declare an induction hypothesis"); return 0; }
    if (!theorem->case_counts[branch]) { x_set_error(header.line, "each Case must contain at least one proof item"); return 0; }
    int saw_hence = 0;
    for (size_t i = 0; i < theorem->case_counts[branch]; i++) {
        XLine item = theorem->case_lines[branch][i];
        if (i + 1 == theorem->case_counts[branch]) {
            int is_hence;
            if (!x_parse_step(&item, &facts, 1, target, scope, scope_count, &is_hence)) return 0;
            if (!is_hence) return 0;
            saw_hence = 1;
        } else {
            int is_hence;
            if (!x_parse_step(&item, &facts, 0, target, scope, scope_count, &is_hence)) return 0;
            if (is_hence) { x_set_error(item.line, "Hence must be the final item in a Case"); return 0; }
        }
    }
    if (!saw_hence) { x_set_error(header.line, "Case is missing its final Hence"); return 0; }
    return 1;
}

static int x_check_theorem(XTheorem *theorem, int transparent, int notation) {
    char *base_kind = NULL, *base_var = NULL, *base_ih_name = NULL;
    char *succ_kind = NULL, *succ_var = NULL, *succ_ih_name = NULL;
    XEq base_ih = {0}, succ_ih = {0}; int base_has_ih = 0, succ_has_ih = 0;
    if (!theorem->let_count) { x_set_error(theorem->line, "Theorem requires at least one 'Let ... be Nat.' binder"); return 0; }
    {
        int induction_is_bound = 0;
        for (size_t i = 0; i < theorem->let_count; i++) if (strcmp(theorem->lets[i], theorem->induction_var) == 0) induction_is_bound = 1;
        if (!induction_is_bound) { x_set_error(theorem->line, "induction variable must be declared by Let"); return 0; }
        if (!x_eq_scoped(theorem->claim, theorem->lets, theorem->let_count)) { x_set_error(theorem->line, "Claim contains an undeclared Nat variable"); return 0; }
    }
    if (theorem->case_count != 2) { x_set_error(theorem->line, "Nat induction requires exactly the zero and successor cases"); return 0; }
    if (!x_parse_case_header(theorem->case_headers[0], &base_kind, &base_var, &base_ih_name, &base_ih, &base_has_ih)) return 0;
    if (!x_parse_case_header(theorem->case_headers[1], &succ_kind, &succ_var, &succ_ih_name, &succ_ih, &succ_has_ih)) return 0;
    if (strcmp(base_kind, theorem->induction_var) != 0 || strcmp(succ_kind, theorem->induction_var) != 0) {
        x_set_error(theorem->case_headers[0].line, "Case variable must match the induction variable"); return 0;
    }
    if (strcmp(base_var, "Nat.zero") != 0) { x_set_error(theorem->case_headers[0].line, "first induction Case must be Nat.zero"); return 0; }
    if (!starts_with(succ_var, "Nat.succ ")) { x_set_error(theorem->case_headers[1].line, "second induction Case must be Nat.succ variable"); return 0; }
    char *k = trim_copy(succ_var + strlen("Nat.succ "));
    if (!valid_name(k) || strchr(k, '.') || strchr(k, ' ')) { x_set_error(theorem->case_headers[1].line, "successor Case pattern must bind one variable"); return 0; }
    for (size_t i = 0; i < theorem->let_count; i++) if (strcmp(k, theorem->lets[i]) == 0) { x_set_error(theorem->case_headers[1].line, "successor Case variable must be fresh"); return 0; }
    XTerm *zero = x_term(X_ZERO, NULL, NULL, NULL);
    XTerm *succ = x_term(X_SUCC, NULL, x_term(X_VAR, k, NULL, NULL), NULL);
    if (!x_check_case(theorem, 0, zero, NULL, 0, base_ih_name, base_ih, base_has_ih, transparent, notation)) return 0;
    if (!x_check_case(theorem, 1, succ, k, 1, succ_ih_name, succ_ih, succ_has_ih, transparent, notation)) return 0;
    return 1;
}

static int x_check_extended(const char *source, int *handled) {
    XLine *lines = NULL; size_t count = 0; int transparent = 0, notation = 0;
    XTheorem theorem; memset(&theorem, 0, sizeof theorem);
    *handled = 0;
    if (!strstr(source, "Transparent ") && !strstr(source, "Notation ") && !strstr(source, "By induction")) return 0;
    *handled = 1;
    if (!x_parse_lines(source, &lines, &count)) goto error;
    size_t i = 0; int found_theorem = 0; int found_print = 0; char *printed_name = NULL;
    while (i < count) {
        XLine line = lines[i];
        if (!line.text[0]) { i++; continue; }
        if (line.indent != 0) { x_set_error(line.line, "top-level declarations must start in column 1"); goto error; }
        if (starts_with(line.text, "Transparent ") || starts_with(line.text, "Notation ")) {
            if (found_theorem) { x_set_error(line.line, "Transparent and Notation declarations must precede the theorem"); goto error; }
            if (starts_with(line.text, "Transparent ") && transparent) { x_set_error(line.line, "duplicate Transparent declaration"); goto error; }
            if (starts_with(line.text, "Notation ") && notation) { x_set_error(line.line, "duplicate Notation declaration"); goto error; }
            if (!x_parse_preamble_line(&line, &transparent, &notation)) goto error;
            i++; continue;
        }
        if (starts_with(line.text, "Theorem ")) {
            if (found_theorem) { x_set_error(line.line, "this checker accepts one theorem per extended source file"); goto error; }
            found_theorem = 1; theorem.line = line.line;
            theorem.name = remove_final_period(line.text + 8);
            if (!valid_name(theorem.name)) { x_set_error(line.line, "malformed Theorem header"); goto error; }
            i++;
            while (i < count && !lines[i].text[0]) i++;
            if (i >= count || lines[i].indent != 2 || !starts_with(lines[i].text, "Let ")) { x_set_error(i < count ? lines[i].line : line.line, "expected an indented 'Let ... be Nat.' declaration"); goto error; }
            {
                char *let = trim_copy(lines[i].text + 4); size_t n = strlen(let);
                if (n && let[n - 1] == '.') let[n - 1] = '\0';
                char *be = strstr(let, " be Nat");
                if (!be) { x_set_error(lines[i].line, "only Nat binders are supported in this theorem"); goto error; }
                *be = '\0';
                char *cursor = let;
                while (*cursor) {
                    char *comma = strchr(cursor, ','); char *var;
                    if (comma) *comma = '\0';
                    var = trim_copy(cursor);
                    if (!valid_name(var)) { x_set_error(lines[i].line, "invalid Let binder"); goto error; }
                    for (size_t j = 0; j < theorem.let_count; j++) {
                        if (strcmp(theorem.lets[j], var) == 0) { x_set_error(lines[i].line, "duplicate Let binder '%s'", var); goto error; }
                    }
                    theorem.lets = (char **)xrealloc(theorem.lets, (theorem.let_count + 1) * sizeof *theorem.lets);
                    theorem.lets[theorem.let_count++] = var;
                    if (!comma) break;
                    cursor = comma + 1;
                }
            }
            i++;
            while (i < count && !lines[i].text[0]) i++;
            if (i >= count || lines[i].indent != 2 || !starts_with(lines[i].text, "Claim:")) { x_set_error(i < count ? lines[i].line : line.line, "expected 'Claim: equality.' after Let"); goto error; }
            {
                char *claim = remove_final_period(trim_copy(lines[i].text + 6)); int ok;
                theorem.claim = x_parse_eq(claim, lines[i].line, &ok); if (!ok) goto error;
            }
            i++;
            while (i < count && !lines[i].text[0]) i++;
            if (i >= count || lines[i].indent != 2 || (strcmp(lines[i].text, "Proof.") != 0 && strcmp(lines[i].text, "Proof") != 0)) { x_set_error(i < count ? lines[i].line : line.line, "expected 'Proof.' after Claim"); goto error; }
            i++;
            while (i < count && !lines[i].text[0]) i++;
            if (i >= count || lines[i].indent != 4 || !starts_with(lines[i].text, "By induction on ")) { x_set_error(i < count ? lines[i].line : line.line, "expected an indented 'By induction on variable.'"); goto error; }
            theorem.induction_var = remove_final_period(lines[i].text + strlen("By induction on "));
            if (!valid_name(theorem.induction_var)) { x_set_error(lines[i].line, "invalid induction variable"); goto error; }
            i++;
            while (i < count && !lines[i].text[0]) i++;
            while (i < count && lines[i].indent == 4 && starts_with(lines[i].text, "Case ")) {
                size_t branch = theorem.case_count;
                if (branch >= 2) { x_set_error(lines[i].line, "duplicate or extra induction Case"); goto error; }
                theorem.case_headers[branch] = lines[i]; theorem.case_count++; i++;
                while (i < count && !lines[i].text[0]) i++;
                while (i < count && lines[i].indent > 4) {
                    if (lines[i].indent != 6) { x_set_error(lines[i].line, "Case proof items must be indented by six spaces"); goto error; }
                    reserve_array((void **)&theorem.case_lines[branch], &theorem.case_caps[branch], theorem.case_counts[branch] + 1, sizeof *theorem.case_lines[branch]);
                    theorem.case_lines[branch][theorem.case_counts[branch]++] = lines[i]; i++;
                    while (i < count && !lines[i].text[0]) i++;
                }
            }
            if (i >= count || lines[i].indent != 2 || (strcmp(lines[i].text, "QED.") != 0 && strcmp(lines[i].text, "QED") != 0)) { x_set_error(i < count ? lines[i].line : line.line, "expected 'QED.' after induction Cases"); goto error; }
            i++;
            if (!x_check_theorem(&theorem, transparent, notation)) goto error;
            continue;
        }
        if (starts_with(line.text, "Print axioms ")) {
            if (found_print) { x_set_error(line.line, "duplicate Print axioms command"); goto error; }
            found_print = 1; printed_name = remove_final_period(line.text + strlen("Print axioms "));
            if (!valid_name(printed_name)) { x_set_error(line.line, "Print axioms expects a name"); goto error; }
            i++; continue;
        }
        x_set_error(line.line, "unsupported top-level item in the extended Nat/equality checker"); goto error;
    }
    if (!found_theorem) { x_set_error(1, "expected a Theorem declaration"); goto error; }
    if (found_print && strcmp(printed_name, theorem.name) != 0) { x_set_error(1, "Print axioms target does not match the theorem in this file"); goto error; }
    printf("checked: %s: %s\n", theorem.name, x_format_eq(theorem.claim));
    if (found_print) printf("%s: axioms = none; unfinished = none\n", theorem.name);
    puts("file certified for the supported LRS-Alpha Nat/equality induction fragment");
    return 0;
error:
    if (g_error_line) fprintf(stderr, "lloyd: line %d: %s\n", g_error_line, g_error);
    else fprintf(stderr, "lloyd: %s\n", g_error[0] ? g_error : "invalid extended source");
    return 1;
}
