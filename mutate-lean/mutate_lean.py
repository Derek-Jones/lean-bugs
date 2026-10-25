#!/usr/bin/env python3
"""
mutate_lean.py -- accumulate the largest possible number of small mutations
in a verified Lean 4 proof while it remains verified.

Usage:   python3 mutate_lean.py config.json

A mutant changes one or two Lean lexical tokens (substitution, insertion,
deletion or reordering) or, for ~10% of mutants, one complete tactic
statement.  Each candidate is checked by a Lean verification oracle; a
candidate is kept only if the proof is still "verified":

    no errors, no `declaration uses 'sorry'` warning, and every theorem's
    `#print axioms` set equal to that of the original proof.

A timeout counts as a change of verified status.  See README.md for the
configuration format, the log format and the list of outstanding issues.
"""

from __future__ import annotations

import dataclasses
import datetime as _dt
import difflib
import hashlib
import json
import os
import random
import re
import shutil
import signal
import stat
import subprocess
import sys
import time
import unicodedata
from typing import Dict, List, Optional, Sequence, Tuple

# ---------------------------------------------------------------------------
# Rules from the specification
# ---------------------------------------------------------------------------

# Words a mutant may never introduce (the count in the mutated proof must not
# exceed the count in the original).  Covers sorry/admit/axioms, the listed
# escape hatches, and every way of starting a new declaration or command.
FORBIDDEN_WORDS = {
    "sorry", "admit", "axiom", "axioms",
    "native_decide", "implemented_by", "set_option", "csimp", "unsafe",
    "opaque", "extern", "ofReduceBool", "Lean.ofReduceBool", "reduceBool",
    "Lean.ofReduceNat", "ofReduceNat", "decide!",
    "macro", "macro_rules", "notation", "infix", "infixl", "infixr",
    "prefix", "postfix", "syntax", "elab", "elab_rules", "instance",
    "declare_syntax_cat", "attribute", "initialize", "builtin_initialize",
    "theorem", "lemma", "def", "example", "abbrev", "structure", "class",
    "inductive", "coinductive", "namespace", "section", "end", "open",
    "variable", "universe", "import", "export", "mutual", "deriving",
    "local", "scoped", "private", "protected", "noncomputable", "partial",
    "nonrec", "run_cmd", "run_tac", "run_elab", "run_meta", "by_elab",
    "elab_tactic", "trust", "debug.skipKernelTC", "omit", "include",
}
FORBIDDEN_SYMBOLS = {"@[", "#"}            # attributes, #commands

# Insertions/substitutions whose only effect is a no-op ("trivial" mutants).
TRIVIAL_WORDS = {"skip", "done", "trace_state", "trace", "dbg_trace",
                 "with_reducible_and_instances", "checkpoint", "save",
                 "sleep", "stop"}

# Top-level commands that end a declaration body.
COMMAND_WORDS = {
    "theorem", "lemma", "def", "example", "abbrev", "instance", "structure",
    "class", "inductive", "axiom", "opaque", "namespace", "section", "end",
    "open", "variable", "universe", "import", "export", "mutual", "set_option",
    "attribute", "macro", "macro_rules", "syntax", "notation", "infix",
    "infixl", "infixr", "prefix", "postfix", "elab", "elab_rules",
    "private", "protected", "noncomputable", "partial", "unsafe", "nonrec",
    "local", "scoped", "deriving", "initialize", "omit", "include",
    "declare_syntax_cat", "add_decl_doc", "termination_by?",
}
PROOF_DECL_WORDS = {"theorem", "lemma", "example"}

BINOP_GROUPS = [
    ["+", "-", "*", "/", "%", "^"],
    ["=", "≠", "<", ">", "≤", "≥", "<=", ">=", "!=", "=="],
    ["∧", "∨", "→", "↔", "->", "<->", "&&", "||"],
    ["∪", "∩", "\\", "⊆", "⊂", "∈", "∉", "×ˢ"],
    ["++", "∣", "∘", "•", "*>", "<*", "<$>", "<*>", ">>=", "|>.", "∑", "∏"],
]
BINOPS = {op for g in BINOP_GROUPS for op in g} - {"∑", "∏", "|>."}

KEYWORDS = {
    "by", "at", "with", "fun", "λ", "do", "then", "else", "if", "match",
    "let", "have", "show", "from", "in", "using", "generalizing", "only",
    "calc", "where", "suffices", "this", "obtain", "rcases", "intro",
    "termination_by", "decreasing_by", "Type", "Prop", "Sort",
}

# A small, non-exhaustive list used to separate tactic names from ordinary
# identifiers when choosing substitutes.  Tactic-position identifiers that
# appear in the proof are added at run time.
KNOWN_TACTICS = {
    "simp", "simp_all", "simpa", "dsimp", "rw", "rwa", "erw", "exact",
    "apply", "refine", "intro", "intros", "rintro", "cases", "rcases",
    "obtain", "induction", "constructor", "left", "right", "exfalso",
    "contradiction", "assumption", "rfl", "decide", "omega", "linarith",
    "nlinarith", "positivity", "ring", "ring_nf", "norm_num", "field_simp",
    "exists", "use", "refine'", "specialize", "subst", "unfold",
    "split", "by_cases", "by_contra", "push_neg", "calc", "show",
    "have", "let", "suffices", "funext", "ext", "congr", "gcongr",
    "trivial", "aesop", "tauto", "norm_cast", "push_cast", "exact_mod_cast",
    "apply_fun", "nth_rewrite", "nth_rw", "conv", "change", "clear",
    "revert", "generalize", "symm", "trans", "first", "repeat", "try",
    "all_goals", "any_goals", "focus", "case", "next", "injection",
    "exists", "constructorm", "casesm", "simp_arith", "bv_omega",
}

SYMBOLS = sorted([
    ":=", "=>", "<;>", "->", "<-", "<->", "←", "→", "↔", "≤", "≥", "≠",
    "<=", ">=", "!=", "==", "&&", "||", "++", "::", "...", "..", "⟨", "⟩",
    "<|>", "<|", "|>.", "|>", "<$>", "<*>", "*>", "<*", ">>=", ">>", "^^^",
    "&&&", "|||", "@[", "%[", "×ˢ", "⁻¹", "∘", "∣", "•", "▸", "⦃", "⦄",
    "‹", "›", "·", "∀", "∃", "∃!", "¬", "∧", "∨", "∈", "∉", "⊆", "⊂", "∪",
    "∩", "∑", "∏", "λ", "Π", "Σ", "?_", "$", "..=",
], key=len, reverse=True)

SUBSCRIPTS = set("₀₁₂₃₄₅₆₇₈₉ₐₑₒₓₔₕₖₗₘₙₚₛₜᵢᵣᵤᵥᵦᵧᵨᵩᵪⱼ")


# ---------------------------------------------------------------------------
# Lexer
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class Tok:
    text: str
    pre: str            # whitespace and comments before the token (trivia)
    kind: str           # ident, num, str, char, sym, field
    uid: int            # identity used for reversal tracking
    line: int = 0       # 1-based line in the text the token came from
    col: int = 0        # 0-based column
    inserted: bool = False   # inserted by a mutant


def _is_id_start(c: str) -> bool:
    if c in "λΠΣ":
        return False
    return c == "_" or c.isalpha() or (
        "Letterlike" in unicodedata.name(c, "") if ord(c) > 127 else False)


def _is_id_rest(c: str) -> bool:
    return _is_id_start(c) or c.isdigit() or c in "'!?" or c in SUBSCRIPTS


class LexError(Exception):
    pass


def tokenize(src: str, uid_start: int = 0) -> Tuple[List[Tok], str]:
    """Split Lean source into tokens; returns (tokens, trailing trivia).
    Rendering with render() reproduces the source exactly."""
    toks: List[Tok] = []
    i, n = 0, len(src)
    line, col = 1, 0
    uid = uid_start

    def advance(s: str):
        nonlocal line, col
        nl = s.count("\n")
        if nl:
            line += nl
            col = len(s) - s.rfind("\n") - 1
        else:
            col += len(s)

    while i < n:
        # ---- trivia ------------------------------------------------------
        j = i
        while j < n:
            c = src[j]
            if c in " \t\r\n":
                j += 1
            elif src.startswith("--", j):
                k = src.find("\n", j)
                j = n if k < 0 else k
            elif src.startswith("/-", j):
                depth, k = 1, j + 2
                while k < n and depth:
                    if src.startswith("/-", k):
                        depth += 1
                        k += 2
                    elif src.startswith("-/", k):
                        depth -= 1
                        k += 2
                    else:
                        k += 1
                if depth:
                    raise LexError(f"unterminated block comment at line {src.count(chr(10), 0, j) + 1}")
                j = k
            else:
                break
        pre = src[i:j]
        advance(pre)
        i = j
        if i >= n:
            return toks, pre
        # ---- token -------------------------------------------------------
        c = src[i]
        start_line, start_col = line, col
        prev = toks[-1] if toks else None
        attached = prev is not None and pre == ""
        if c == '"':
            k = i + 1
            while k < n and src[k] != '"':
                k += 2 if src[k] == "\\" else 1
            if k >= n:
                raise LexError(f"unterminated string at line {line}")
            text, kind = src[i:k + 1], "str"
        elif c == "'" and not (attached and prev.kind == "ident") and \
                re.match(r"'(\\.[^']*|[^'\\])'", src[i:]):
            text, kind = re.match(r"'(\\.[^']*|[^'\\])'", src[i:]).group(0), "char"
        elif c == "." and attached and prev.kind in ("ident", "field", "sym") \
                and (prev.kind != "sym" or prev.text in (")", "⟩", "]")) \
                and i + 1 < n and src[i + 1].isdigit():
            m = re.match(r"\.\d+", src[i:])
            text, kind = m.group(0), "field"
        elif c.isdigit():
            m = re.match(r"0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|"
                         r"\d[\d_]*(\.\d+)?([eE][+-]?\d+)?", src[i:])
            text, kind = m.group(0), "num"
        elif c == "«" or _is_id_start(c):
            k = i
            while True:
                if k < n and src[k] == "«":
                    e = src.find("»", k)
                    if e < 0:
                        raise LexError(f"unterminated «» at line {line}")
                    k = e + 1
                elif k < n and _is_id_start(src[k]):
                    k += 1
                    while k < n and _is_id_rest(src[k]):
                        k += 1
                else:
                    break
                if k + 1 < n and src[k] == "." and (
                        _is_id_start(src[k + 1]) or src[k + 1] == "«"):
                    k += 1
                    continue
                break
            text, kind = src[i:k], "ident"
        elif c == "#" and i + 1 < n and _is_id_start(src[i + 1]):
            m = re.match(r"#[A-Za-z_]+", src[i:])
            text, kind = m.group(0), "sym"
        elif c == "?" and i + 1 < n and _is_id_start(src[i + 1]):
            m = re.match(r"\?[^\s()\[\]{},:]+", src[i:])
            text, kind = m.group(0), "ident"
        else:
            for s in SYMBOLS:
                if src.startswith(s, i):
                    text = s
                    break
            else:
                text = c
            kind = "sym"
        toks.append(Tok(text, pre, kind, uid, start_line, start_col))
        uid += 1
        advance(text)
        i += len(text)
    return toks, ""


def render(toks: Sequence[Tok], trailer: str) -> str:
    return "".join(t.pre + t.text for t in toks) + trailer


def at_line_start(t: Tok, is_first: bool) -> bool:
    return is_first or "\n" in t.pre


def indent_of(t: Tok) -> int:
    if "\n" not in t.pre:
        return -1
    return len(t.pre) - t.pre.rfind("\n") - 1


# ---------------------------------------------------------------------------
# Declarations: which tokens may be mutated
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class Decl:
    keyword: str
    name: Optional[str]
    head_start: int      # index of first token of the declaration (modifiers)
    body_start: int      # first token after the top-level ':='
    body_end: int        # one past the last token of the body


OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄", "‹": "›", "%[": "]"}
CLOSE = {v for v in OPEN.values()}


def is_command_start(toks: Sequence[Tok], i: int) -> bool:
    t = toks[i]
    if not ((i == 0 and "\n" not in t.pre and t.pre.strip(" \t") == t.pre.strip())
            or indent_of(t) == 0):
        return False
    if t.kind == "ident" and t.text in COMMAND_WORDS:
        return True
    if t.text in ("@[",) or (t.kind == "sym" and t.text.startswith("#")):
        return True
    if t.text.startswith("/--"):
        return True
    return False


def find_decls(toks: Sequence[Tok]) -> List[Decl]:
    """Locate theorem/lemma/example declarations and their proof bodies."""
    starts = [i for i in range(len(toks)) if is_command_start(toks, i)]
    starts.append(len(toks))
    decls = []
    for a, b in zip(starts, starts[1:]):
        # skip modifiers/attributes to the declaration keyword
        k = a
        while k < b and not (toks[k].kind == "ident" and
                             toks[k].text in PROOF_DECL_WORDS | {"def", "abbrev",
                                                                 "instance", "structure",
                                                                 "inductive", "class"}):
            k += 1
        if k >= b or toks[k].text not in PROOF_DECL_WORDS:
            continue
        kw = toks[k].text
        name = None
        if kw != "example" and k + 1 < b and toks[k + 1].kind == "ident":
            name = toks[k + 1].text
        depth, body = 0, None
        for m in range(k + 1, b):
            x = toks[m].text
            if x in OPEN:
                depth += 1
            elif x in CLOSE:
                depth = max(0, depth - 1)
            elif depth == 0 and x == ":=":
                body = m + 1
                break
            elif depth == 0 and x == "|" and at_line_start(toks[m], False):
                body = m
                break
        if body is None or body >= b:
            continue
        decls.append(Decl(kw, name, a, body, b))
    return decls


def statement_spans(toks: Sequence[Tok], d: Decl,
                    split_inline: bool = True) -> List[Tuple[int, int]]:
    """Tactic/term statements inside a proof body: each starts at a token that
    begins a line, or follows `by`, `·` or `=>` on the same line, at bracket
    depth 0, and runs up to the next such start.  Child blocks are separate
    statements.  With split_inline=False only `by` starts an inline statement
    (a bullet and its tactic stay together; used by statement mutants)."""
    triggers = ("by", "·", "=>") if split_inline else ("by",)
    starts, depth = [], 0
    for i in range(d.body_start, d.body_end):
        t = toks[i]
        if depth == 0 and (("\n" in t.pre) or
                           (i > d.body_start and toks[i - 1].text in triggers)):
            if t.text not in CLOSE and t.text != "by":
                starts.append(i)
        if t.text in OPEN:
            depth += 1
        elif t.text in CLOSE:
            depth = max(0, depth - 1)
    spans = []
    for j, s in enumerate(starts):
        e = starts[j + 1] if j + 1 < len(starts) else d.body_end
        spans.append((s, e))
    return spans


def stmt_indent(toks: Sequence[Tok], s: int) -> int:
    """Indentation of a statement: its line indent, or its column when it
    follows `by`/`·`/`=>` on the same line."""
    return indent_of(toks[s]) if "\n" in toks[s].pre else 10_000 + s


def enclosing_blocks(toks: Sequence[Tok], k: int) -> List[Tuple[int, int]]:
    """Statement blocks containing token k, innermost first.  A block is a
    statement plus the more-indented statements (children) that follow it.
    The whole proof body is not included (removing it can never verify)."""
    for d in find_decls(toks):
        if not d.body_start <= k < d.body_end:
            continue
        spans = statement_spans(toks, d)
        blocks = []
        for j, (s, e) in enumerate(spans):
            ind = stmt_indent(toks, s)
            end = e
            for s2, e2 in spans[j + 1:]:
                if "\n" in toks[s2].pre and indent_of(toks[s2]) <= (
                        ind if ind < 10_000 else toks[s].col):
                    break
                end = e2
            if s <= k < end and not (s == spans[0][0] and end == d.body_end):
                blocks.append((s, end))
        blocks.sort(key=lambda b: b[1] - b[0])
        return blocks
    return []


def remove_block(toks: Sequence[Tok], s: int, e: int) -> List[Tok]:
    out = [dataclasses.replace(t) for t in toks[:s]] + \
          [dataclasses.replace(t) for t in toks[e:]]
    if e < len(toks) and s < len(toks) and "\n" not in toks[e].pre:
        out[s].pre = toks[s].pre
    return out


# ---------------------------------------------------------------------------
# Mutation state and history (for the "no reversal" rule)
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class History:
    values: Dict[int, set] = dataclasses.field(default_factory=dict)   # uid -> texts held
    swapped: set = dataclasses.field(default_factory=set)              # frozenset of uids
    deleted: List[Tuple[Optional[int], Optional[int], Tuple[str, ...]]] = \
        dataclasses.field(default_factory=list)                         # (prev, next, texts)
    states: set = dataclasses.field(default_factory=set)               # token-sequence hashes

    def copy(self) -> "History":
        return History({k: set(v) for k, v in self.values.items()},
                       set(self.swapped), list(self.deleted), set(self.states))


def state_hash(toks: Sequence[Tok]) -> str:
    return hashlib.sha256("\x00".join(t.text for t in toks).encode()).hexdigest()


@dataclasses.dataclass
class Mutant:
    kind: str
    description: str
    toks: List[Tok]
    new_texts: List[str]            # texts introduced (for trivial / forbidden checks)
    history: History
    touched: List[int] = dataclasses.field(default_factory=list)  # uids in toks at the change
    script: List[dict] = dataclasses.field(default_factory=list)  # replayable edit script


class Reject(Exception):
    """Raised when a generated candidate breaks a rule (never sent to Lean)."""


class Mutator:
    """Generates mutants of one private proof.

    A mutant is generated as an *edit script*: a list of primitive edits that
    refer to tokens by uid (original tokens have the same uid in every process,
    inserted tokens get uids from a per-process range).  apply_script() runs a
    script against the current proof, enforcing every rule; the same function
    replays scripts shared by other processes."""

    def __init__(self, toks: List[Tok], trailer: str, rng: random.Random,
                 statement_fraction: float, reject_dead_code: bool = True,
                 uid_base: Optional[int] = None):
        self.rng = rng
        self.reject_dead_code = reject_dead_code
        self.trailer = trailer
        self.statement_fraction = statement_fraction
        self.orig_toks = [dataclasses.replace(t) for t in toks]
        self.orig_counts = self._forbidden_counts(toks)
        self.next_uid = (uid_base if uid_base is not None
                         else max((t.uid for t in toks), default=0) + 1)
        self.history = History()
        for t in toks:
            self.history.values[t.uid] = {t.text}
        self.history.states.add(state_hash(toks))
        self.orig_heads = self._heads(toks)
        # pools of material "used within the proof"
        in_decls = [t for d in find_decls(toks) for t in toks[d.head_start:d.body_end]]
        self.idents = sorted({t.text for t in in_decls if t.kind == "ident"
                              and t.text not in FORBIDDEN_WORDS | KEYWORDS
                              | TRIVIAL_WORDS})
        tactic_pos = set()
        for d in find_decls(toks):
            for s, _ in statement_spans(toks, d):
                if toks[s].kind == "ident":
                    tactic_pos.add(toks[s].text)
        self.tactics = sorted((tactic_pos | (KNOWN_TACTICS & set(self.idents)))
                              - FORBIDDEN_WORDS - TRIVIAL_WORDS)
        self.terms = sorted(set(self.idents) - set(self.tactics))
        self.binops_used = sorted({t.text for t in in_decls if t.text in BINOPS})

    # -- rule checks ---------------------------------------------------------
    @staticmethod
    def _forbidden_counts(toks: Sequence[Tok]) -> Dict[str, int]:
        c: Dict[str, int] = {}
        for t in toks:
            words = {t.text} | set(t.text.split("."))
            for w in words:
                if w in FORBIDDEN_WORDS:
                    c[w] = c.get(w, 0) + 1
            if t.text in FORBIDDEN_SYMBOLS or t.text.startswith("#"):
                c[t.text] = c.get(t.text, 0) + 1
        return c

    @staticmethod
    def _heads(toks: Sequence[Tok]) -> List[Tuple[str, ...]]:
        """Token texts of every declaration header (statement + type)."""
        return [tuple(t.text for t in toks[d.head_start:d.body_start])
                for d in find_decls(toks)]

    def check(self, m: Mutant, cur: Sequence[Tok]) -> None:
        new = m.toks
        if state_hash(new) in self.history.states:
            raise Reject("returns the proof to an earlier state (reversal)")
        if [t.text for t in new] == [t.text for t in cur]:
            raise Reject("no token change (whitespace/comment only)")
        counts = self._forbidden_counts(new)
        for w, c in counts.items():
            if c > self.orig_counts.get(w, 0):
                raise Reject(f"introduces forbidden token {w!r}")
        for txt in m.new_texts:
            if txt in TRIVIAL_WORDS or txt.split(".")[-1] in TRIVIAL_WORDS:
                raise Reject(f"trivial mutant ({txt!r})")
        if self._heads(new) != self.orig_heads:
            raise Reject("changes a theorem statement or the declaration structure")
        body = set(self._mutable_indices(cur))
        where = {t.uid: i for i, t in enumerate(cur)}
        for prim in m.script:
            for u in _script_uids(prim):
                if u in where and where[u] not in body:
                    raise Reject("edits a token outside the proof bodies")

    # -- helpers ---------------------------------------------------------------
    def _mutable_indices(self, toks: Sequence[Tok]) -> List[int]:
        idx = []
        for d in find_decls(toks):
            idx.extend(range(d.body_start, d.body_end))
        return idx

    def _new_tok(self, text: str, pre: str, kind: Optional[str] = None) -> Tok:
        t = Tok(text, pre, kind or classify(text), self.next_uid, inserted=True)
        self.next_uid += 1
        return t

    def _substitute_text(self, t: Tok) -> Optional[str]:
        r = self.rng
        if t.text in BINOPS:
            same = next(g for g in BINOP_GROUPS if t.text in g)
            pool = [o for o in (same if r.random() < 0.7 else sorted(BINOPS))
                    if o != t.text]
            return r.choice(pool) if pool else None
        if t.kind == "num":
            try:
                v = int(t.text.replace("_", ""), 0)
            except ValueError:
                return None
            return str(r.choice([v + 1, max(v - 1, 0), 0, 1, 2, v * 2]))
        if t.kind == "ident" and t.text not in KEYWORDS:
            pool = self.tactics if t.text in self.tactics else self.terms
            pool = [x for x in pool if x != t.text]
            return r.choice(pool) if pool else None
        return None

    def _pool_token(self) -> str:
        r = self.rng
        choice = r.random()
        if choice < 0.55 and self.terms:
            return r.choice(self.terms)
        if choice < 0.75 and self.binops_used:
            return r.choice(self.binops_used)
        if choice < 0.85 and self.tactics:
            return r.choice(self.tactics)
        return r.choice(["←", "!", "¬", "_", "0", "1", ",", "*", "at", "only"])

    def _swap_class(self, t: Tok) -> Optional[str]:
        if t.text in BINOPS:
            return "binop"
        if t.kind == "num":
            return "num"
        if t.kind == "ident" and t.text not in KEYWORDS:
            return "tactic" if t.text in self.tactics else "term"
        return None

    @staticmethod
    def _substitutable(t: Tok) -> bool:
        return t.text in BINOPS or t.kind == "num" or (
            t.kind == "ident" and t.text not in KEYWORDS)

    # -- choosing a random token-level edit -------------------------------------
    def token_script(self, cur: List[Tok]) -> Tuple[str, str, List[dict]]:
        r = self.rng
        idx = self._mutable_indices(cur)
        if not idx:
            raise Reject("no mutable tokens")
        op = r.choices(
            ["subst1", "subst2", "delete1", "delete2", "insert1", "insert2",
             "swap_adjacent", "swap_pair"],
            weights=[30, 8, 14, 5, 14, 6, 13, 10])[0]

        def subst(i: int) -> dict:
            nt = self._substitute_text(cur[i])
            if nt is None or nt == cur[i].text:
                raise Reject("no substitute available")
            return {"op": "subst", "uid": cur[i].uid, "old": cur[i].text, "new": nt}

        if op == "subst1":
            cand = [i for i in idx if self._substitutable(cur[i])]
            if not cand:
                raise Reject("nothing substitutable")
            i = r.choice(cand)
            e = subst(i)
            return op, f"substitute {e['old']!r} -> {e['new']!r} at {pos(cur[i])}", [e]
        if op == "subst2":
            cand = [i for i in idx if self._substitutable(cur[i])]
            if len(cand) < 2:
                raise Reject("nothing substitutable")
            i = r.choice(cand)
            near = [j for j in cand if j != i and abs(j - i) <= 6]
            if not near:
                raise Reject("no second token nearby")
            j = r.choice(near)
            e1, e2 = subst(i), subst(j)
            return op, (f"substitute {e1['old']!r} -> {e1['new']!r} at {pos(cur[i])} and "
                        f"{e2['old']!r} -> {e2['new']!r} at {pos(cur[j])}"), [e1, e2]
        if op in ("delete1", "delete2"):
            cnt = 1 if op == "delete1" else 2
            cand = [i for i in idx if i + cnt - 1 in idx and i + cnt <= len(cur)]
            if not cand:
                raise Reject("nothing to delete")
            i = r.choice(cand)
            span = cur[i:i + cnt]
            return op, f"delete {' '.join(t.text for t in span)!r} at {pos(cur[i])}", [
                {"op": "delete", "uids": [t.uid for t in span],
                 "old": [t.text for t in span]}]
        if op in ("insert1", "insert2"):
            i = r.choice(idx)
            if op == "insert1":
                texts = [self._pool_token()]
            elif r.random() < 0.5:
                # a bigram taken from the proof
                j = r.choice(idx[:-1]) if len(idx) > 1 else idx[0]
                if j + 1 >= len(cur):
                    raise Reject("no bigram")
                texts = [cur[j].text, cur[j + 1].text]
            else:
                lead = r.choice(["←", ",", "<;>"] + self.binops_used)
                texts = [lead, r.choice(self.terms or self.idents or ["_"])]
            return op, (f"insert {' '.join(texts)!r} before {cur[i].text!r} at "
                        f"{pos(cur[i])}"), [
                {"op": "insert", "before": cur[i].uid, "before_text": cur[i].text,
                 "texts": texts}]
        if op == "swap_adjacent":
            cand = [i for i in idx if i + 1 in idx and cur[i].text != cur[i + 1].text]
            if not cand:
                raise Reject("nothing to swap")
            i = r.choice(cand)
            j = i + 1
        else:  # swap_pair: two tokens of the same class within a window
            cand = [i for i in idx if self._swap_class(cur[i])]
            if not cand:
                raise Reject("nothing to swap")
            i = r.choice(cand)
            same = [j for j in cand if j != i and abs(j - i) <= 12
                    and self._swap_class(cur[j]) == self._swap_class(cur[i])
                    and cur[j].text != cur[i].text]
            if not same:
                raise Reject("no partner to swap with")
            j = r.choice(same)
        return op, (f"swap {cur[i].text!r} at {pos(cur[i])} <-> {cur[j].text!r} at "
                    f"{pos(cur[j])}"), [
            {"op": "swap", "a": cur[i].uid, "b": cur[j].uid,
             "old": [cur[i].text, cur[j].text]}]

    # -- choosing a random statement-level edit -----------------------------------
    def statement_script(self, cur: List[Tok]) -> Tuple[str, str, List[dict]]:
        r = self.rng
        spans = [(s, e) for d in find_decls(cur)
                 for (s, e) in statement_spans(cur, d, split_inline=False)]
        if not spans:
            raise Reject("no statements")
        ops = ["stmt_delete", "stmt_swap", "stmt_replace"]
        if not self.reject_dead_code:
            # a duplicated statement that still verifies is always removable,
            # so with the dead-code check on it could never be accepted
            ops.append("stmt_duplicate")
        op = r.choice(ops)
        line_spans = [(s, e) for (s, e) in spans if "\n" in cur[s].pre]

        def text_of(s, e):
            return " ".join(t.text for t in cur[s:e])

        def ids(s, e):
            return [t.uid for t in cur[s:e]], [t.text for t in cur[s:e]]

        if op == "stmt_delete":
            s, e = r.choice(spans)
            u, o = ids(s, e)
            return op, f"delete statement {text_of(s, e)!r} at {pos(cur[s])}", [
                {"op": "stmt_delete", "uids": u, "old": o}]
        if op == "stmt_duplicate":
            if not line_spans:
                raise Reject("no line statements")
            s, e = r.choice(line_spans)
            u, o = ids(s, e)
            return op, f"duplicate statement {text_of(s, e)!r} at {pos(cur[s])}", [
                {"op": "stmt_dup", "uids": u, "old": o}]
        if op == "stmt_swap":
            pairs = [(a, b) for a, b in zip(line_spans, line_spans[1:])
                     if a[1] == b[0] and indent_of(cur[a[0]]) == indent_of(cur[b[0]])]
            if not pairs:
                raise Reject("no adjacent statements to swap")
            (s1, e1), (s2, e2) = r.choice(pairs)
            ua, oa = ids(s1, e1)
            ub, ob = ids(s2, e2)
            return op, (f"swap statements {text_of(s1, e1)!r} and {text_of(s2, e2)!r} "
                        f"at {pos(cur[s1])}"), [
                {"op": "stmt_swap", "a": ua, "b": ub, "old_a": oa, "old_b": ob}]
        # stmt_replace
        s, e = r.choice(spans)
        others = [(a, b) for (a, b) in spans if text_of(a, b) != text_of(s, e)]
        if not others:
            raise Reject("no other statement to copy")
        a, b = r.choice(others)
        shift = indent_of(cur[s]) - indent_of(cur[a]) \
            if indent_of(cur[a]) >= 0 and indent_of(cur[s]) >= 0 else 0
        copy = []
        for k, t in enumerate(cur[a:b]):
            pre = t.pre
            if k and "\n" in pre and shift:
                pre = pre[:pre.rfind("\n") + 1] + " " * max(0, indent_of(t) + shift)
            copy.append([t.text, pre, t.kind])
        u, o = ids(s, e)
        return op, (f"replace statement {text_of(s, e)!r} at {pos(cur[s])} with "
                    f"{text_of(a, b)!r}"), [
            {"op": "stmt_replace", "uids": u, "old": o, "copy": copy}]

    # -- applying an edit script ------------------------------------------------------
    def apply_script(self, cur: List[Tok], kind: str, desc: str,
                     script: List[dict]) -> Mutant:
        """Apply `script` to the current proof.  Raises Reject if the script does
        not apply here (anchor tokens missing or changed) or breaks a rule."""
        h = self.history.copy()
        new = [dataclasses.replace(t) for t in cur]
        touched: List[int] = []
        new_texts: List[str] = []

        def where() -> Dict[int, int]:
            return {t.uid: i for i, t in enumerate(new)}

        def span_of(uids: List[int], old: List[str]) -> Tuple[int, int]:
            w = where()
            if not uids or any(u not in w for u in uids):
                raise Reject("not applicable: anchor tokens are not in this proof")
            s = w[uids[0]]
            if [t.uid for t in new[s:s + len(uids)]] != list(uids) or \
                    [t.text for t in new[s:s + len(uids)]] != list(old):
                raise Reject("not applicable: anchor tokens differ in this proof")
            return s, s + len(uids)

        def record_deleted(s: int, e: int) -> None:
            h.deleted.append((new[s - 1].uid if s else None,
                              new[e].uid if e < len(new) else None,
                              tuple(t.text for t in new[s:e])))

        def check_reinsert(i: int, texts: Tuple[str, ...]) -> None:
            prev_uid = new[i - 1].uid if i > 0 else None
            next_uid = new[i].uid if i < len(new) else None
            for (p, q, tx) in h.deleted:
                if tx == texts and (p == prev_uid or q == next_uid):
                    raise Reject("re-inserts deleted text at the same place (reversal)")

        for prim in script:
            op = prim["op"]
            if op == "subst":
                i, _ = span_of([prim["uid"]], [prim["old"]])
                nt = prim["new"]
                if nt in h.values.setdefault(new[i].uid, {new[i].text}):
                    raise Reject("substitution restores an earlier value (reversal)")
                h.values[new[i].uid].add(nt)
                new[i].text = nt
                new[i].kind = "num" if new[i].kind == "num" else classify(nt)
                touched.append(new[i].uid)
                new_texts.append(nt)
            elif op == "delete":
                i, e = span_of(prim["uids"], prim["old"])
                if any(t.inserted for t in new[i:e]):
                    raise Reject("deletes a token inserted by an earlier mutant (reversal)")
                record_deleted(i, e)
                # location of the change: previous token on the same line, else the next
                if i > 0 and "\n" not in new[i].pre:
                    touched.append(new[i - 1].uid)
                elif e < len(new):
                    touched.append(new[e].uid)
                keep_pre = new[i].pre
                if e < len(new):
                    nxt = new[e]
                    if "\n" in keep_pre and "\n" in nxt.pre:
                        pass          # deleted a whole line: keep next line's layout
                    elif "--" in nxt.pre or "/-" in nxt.pre or "\n" in nxt.pre:
                        nxt.pre = keep_pre + nxt.pre.lstrip(" \t")
                    else:
                        nxt.pre = keep_pre
                del new[i:e]
            elif op == "insert":
                i, _ = span_of([prim["before"]], [prim["before_text"]])
                check_reinsert(i, tuple(prim["texts"]))
                nt = [self._new_tok(x, " ") for x in prim["texts"]]
                # keep the layout before the insertion point; always separate the
                # inserted tokens from their neighbours so identifiers cannot merge
                nt[0].pre = new[i].pre if new[i].pre else " "
                new[i].pre = " "
                new[i:i] = nt
                touched.extend(t.uid for t in nt)
                new_texts.extend(prim["texts"])
            elif op == "swap":
                i, _ = span_of([prim["a"]], [prim["old"][0]])
                j, _ = span_of([prim["b"]], [prim["old"][1]])
                key = frozenset((prim["a"], prim["b"]))
                if key in h.swapped:
                    raise Reject("swaps a pair that was swapped before (reversal)")
                h.swapped.add(key)
                a, b = new[i], new[j]
                new[i] = dataclasses.replace(b, pre=a.pre)
                new[j] = dataclasses.replace(a, pre=b.pre)
                touched += [a.uid, b.uid]
            elif op == "stmt_delete":
                s, e = span_of(prim["uids"], prim["old"])
                if any(t.inserted for t in new[s:e]):
                    raise Reject("deletes a statement inserted by an earlier mutant (reversal)")
                record_deleted(s, e)
                if e < len(new) and "\n" not in new[e].pre:
                    new[e].pre = new[s].pre
                del new[s:e]
            elif op == "stmt_dup":
                s, e = span_of(prim["uids"], prim["old"])
                check_reinsert(e, tuple(prim["old"]))
                copy = [self._new_tok(t.text, t.pre, t.kind) for t in new[s:e]]
                new[e:e] = copy
                touched = [t.uid for t in copy]
                new_texts.extend(prim["old"])
            elif op == "stmt_swap":
                s1, e1 = span_of(prim["a"], prim["old_a"])
                s2, e2 = span_of(prim["b"], prim["old_b"])
                if e1 != s2:
                    raise Reject("not applicable: statements are not adjacent here")
                key = frozenset((prim["a"][0], prim["b"][0]))
                if key in h.swapped:
                    raise Reject("swaps statements swapped before (reversal)")
                h.swapped.add(key)
                a = [dataclasses.replace(t) for t in new[s1:e1]]
                b = [dataclasses.replace(t) for t in new[s2:e2]]
                a[0].pre, b[0].pre = new[s2].pre, new[s1].pre
                new[s1:e2] = b + a
                touched = [a[0].uid, b[0].uid]
            elif op == "stmt_replace":
                s, e = span_of(prim["uids"], prim["old"])
                if any(t.inserted for t in new[s:e]):
                    raise Reject("replaces a statement inserted by an earlier mutant (reversal)")
                texts = tuple(c[0] for c in prim["copy"])
                check_reinsert(s, texts)
                record_deleted(s, e)
                copy = [self._new_tok(c[0], c[1], c[2]) for c in prim["copy"]]
                copy[0].pre = new[s].pre
                new[s:e] = copy
                touched = [t.uid for t in copy]
                new_texts.extend(texts)
            else:
                raise Reject(f"unknown edit {op!r}")
        return Mutant(kind, desc, new, new_texts, h, touched, script)

    # -- driver ----------------------------------------------------------------------
    def propose(self, cur: List[Tok], max_tries: int = 500) -> Tuple[Mutant, int]:
        rejected = 0
        for _ in range(max_tries):
            try:
                if self.rng.random() < self.statement_fraction:
                    kind, desc, script = self.statement_script(cur)
                else:
                    kind, desc, script = self.token_script(cur)
                m = self.apply_script(cur, kind, desc, script)
                self.check(m, cur)
                return m, rejected
            except Reject:
                rejected += 1
        raise Reject(f"no valid mutant found in {max_tries} tries")

    def replay(self, cur: List[Tok], kind: str, desc: str, script: List[dict]) -> Mutant:
        """Build a mutant from a script shared by another process (Reject if it
        does not apply to this proof or breaks a rule here)."""
        m = self.apply_script(cur, kind, desc, script)
        self.check(m, cur)
        return m

    def accept(self, m: Mutant) -> None:
        self.history = m.history
        self.history.states.add(state_hash(m.toks))


def _script_uids(prim: dict) -> List[int]:
    out: List[int] = []
    for k in ("uid", "before", "a", "b", "uids"):
        v = prim.get(k)
        if isinstance(v, int):
            out.append(v)
        elif isinstance(v, list):
            out.extend(v)
    return out


def classify(text: str) -> str:
    if text and (text[0] == "«" or _is_id_start(text[0])):
        return "ident"
    if text and text[0].isdigit():
        return "num"
    return "sym"


def pos(t: Tok) -> str:
    return f"L{t.line}:C{t.col}" if t.line else "(inserted)"


# ---------------------------------------------------------------------------
# Verification oracles
# ---------------------------------------------------------------------------

@dataclasses.dataclass
class Verdict:
    verified: bool
    reason: str
    axioms: Dict[str, Tuple[str, ...]]
    seconds: float
    timed_out: bool = False
    output: str = ""


AXIOM_RE = re.compile(r"'((?:[^'\n]|'(?! depends| does not))+)' depends on axioms:\s*\[(.*?)\]",
                      re.S)
NOAXIOM_RE = re.compile(r"'((?:[^'\n]|'(?! depends| does not))+)' does not depend on any axioms")
SORRY_RE = re.compile(r"declaration uses ['`]sorry['`]")
ERROR_RE = re.compile(r":\d+:\d+: error|^error:", re.M)


def with_axiom_probes(toks: List[Tok], trailer: str) -> str:
    """Render the proof with `#print axioms NAME` after every named theorem."""
    return render_probed(toks, trailer)[0]


def render_probed(toks: List[Tok], trailer: str) -> Tuple[str, List[Tuple[int, int]]]:
    """As with_axiom_probes, also returning each token's (1-based line, column)
    in the rendered text, so Lean messages can be mapped back to tokens."""
    decls = {d.body_end: d for d in find_decls(toks) if d.name}
    out: List[str] = []
    where: List[Tuple[int, int]] = []
    line, col = 1, 0

    def emit(x: str):
        nonlocal line, col
        out.append(x)
        nl = x.count("\n")
        if nl:
            line += nl
            col = len(x) - x.rfind("\n") - 1
        else:
            col += len(x)

    for i, t in enumerate(toks):
        if i in decls:
            emit(f"\n\n#print axioms {decls[i].name}\n")
        emit(t.pre)
        where.append((line, col))
        emit(t.text)
    if len(toks) in decls:
        emit(f"\n\n#print axioms {decls[len(toks)].name}\n")
    emit(trailer)
    return "".join(out), where


UNUSED_BINDER_RE = re.compile(
    r":(\d+):(\d+):[^\n]*?(?:unused variable|is not explicitly referenced)")


def unreferenced_binders(output: str, toks: List[Tok], trailer: str) -> set:
    """Indices of binder names Lean reported as unused / not referenced."""
    flagged = {(int(a), int(b)) for a, b in UNUSED_BINDER_RE.findall(output)}
    if not flagged:
        return set()
    _, where = render_probed(toks, trailer)
    return {i for i, p in enumerate(where) if p in flagged}


def pure_pattern_rename(cur: List[Tok], cand: List[Tok]) -> bool:
    """True if cand differs from cur only by renaming variables bound in a
    `| ctor a b =>` alternative that the alternative never mentions (Lean's
    unused-variable linter does not report these)."""
    if len(cur) != len(cand):
        return False
    diff = [i for i, (a, b) in enumerate(zip(cur, cand)) if a.text != b.text]
    if not diff:
        return False
    for i in diff:
        if cur[i].kind != "ident" or cand[i].kind != "ident":
            return False
        alt = None
        for (bs, be) in enclosing_blocks(cand, i):
            if cand[bs].text == "|":
                arrow = next((k for k in range(bs, be) if cand[k].text == "=>"), None)
                if arrow is not None and bs < i < arrow:
                    alt = (bs, be)
                    break
        if alt is None:
            return False
        bs, be = alt
        others = [k for k in range(bs, be) if k not in diff]
        if any(cur[k].text == cur[i].text for k in others) or \
                any(cand[k].text == cand[i].text for k in others):
            return False
    return True


UNUSED_SIMP_RE = re.compile(r":(\d+):(\d+):[^\n]*?This simp argument is unused")


def unused_simp_args(output: str, toks: List[Tok], trailer: str) -> set:
    """Indices of tokens Lean reported as unused simp arguments."""
    flagged = {(int(a), int(b)) for a, b in UNUSED_SIMP_RE.findall(output)}
    if not flagged:
        return set()
    _, where = render_probed(toks, trailer)
    return {i for i, p in enumerate(where) if p in flagged}


def remove_block_and_refs(toks: Sequence[Tok], s: int, e: int,
                          unused: set) -> List[Tok]:
    """remove_block, also dropping the block's `have NAME` from simp argument
    lists where Lean reported it unused (with its separating comma)."""
    name = None
    if toks[s].text == "have" and s + 1 < e and toks[s + 1].kind == "ident":
        name = toks[s + 1].text
    drop = set()
    if name:
        for i in unused:
            if toks[i].text == name and not s <= i < e:
                drop.add(i)
                if i + 1 < len(toks) and toks[i + 1].text == ",":
                    drop.add(i + 1)
                elif i > 0 and toks[i - 1].text == ",":
                    drop.add(i - 1)
    base = remove_block(toks, s, e)
    if not drop:
        return base
    # map indices (all dropped tokens are outside [s, e))
    kept_uids = {toks[i].uid for i in drop}
    return [t for t in base if t.uid not in kept_uids]


def parse_lean_output(text: str) -> Tuple[bool, bool, Dict[str, Tuple[str, ...]]]:
    axioms: Dict[str, Tuple[str, ...]] = {}
    for m in AXIOM_RE.finditer(text):
        axioms[m.group(1)] = tuple(sorted(a.strip() for a in m.group(2).split(",")
                                          if a.strip()))
    for m in NOAXIOM_RE.finditer(text):
        axioms[m.group(1)] = ()
    return bool(ERROR_RE.search(text)), bool(SORRY_RE.search(text)), axioms


def _kill(p: subprocess.Popen) -> None:
    try:
        os.killpg(p.pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass
    try:
        p.wait(timeout=10)
    except subprocess.TimeoutExpired:
        pass


def cfg_num(cfg: dict, key: str, default: float) -> float:
    """Numeric config value; a missing key or JSON null means the default."""
    v = cfg.get(key)
    if v is None:
        return float(default)
    try:
        return float(v)
    except (TypeError, ValueError):
        raise ValueError(f"config value {key!r} must be a number, not {v!r}")


class LeanOracle:
    """Runs `lean FILE` (or `lake env lean FILE` inside a Lake project)."""

    def __init__(self, cfg: dict, proof_path: str, tag: str = ""):
        self.cmd = cfg.get("lean_command") or ["lean"]
        if isinstance(self.cmd, str):
            self.cmd = self.cmd.split()
        self.cwd = cfg.get("project_root") or os.path.dirname(proof_path)
        self.timeout = cfg_num(cfg, "timeout_seconds", 120)
        stem = os.path.splitext(os.path.basename(proof_path))[0]
        self.work = os.path.join(os.path.dirname(proof_path),
                                 f"{stem}_mutant_candidate{tag}.lean")

    def start(self) -> None:
        if shutil.which(self.cmd[0]) is None and not os.path.exists(self.cmd[0]):
            raise RuntimeError(f"Lean command not found: {self.cmd[0]}")

    def stop(self) -> None:
        try:
            os.remove(self.work)
        except OSError:
            pass

    def check(self, source: str, timeout: Optional[float] = None) -> Verdict:
        timeout = self.timeout if timeout is None else timeout
        with open(self.work, "w", encoding="utf-8") as f:
            f.write(source)
        t0 = time.monotonic()
        p = subprocess.Popen(self.cmd + [self.work], cwd=self.cwd, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            out, _ = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            _kill(p)
            return Verdict(False, f"timeout after {timeout:g}s", {},
                           time.monotonic() - t0, timed_out=True)
        dt = time.monotonic() - t0
        has_err, has_sorry, ax = parse_lean_output(out)
        if has_err or (p.returncode != 0 and not has_sorry):
            first = next((l for l in out.splitlines() if "error" in l), out[:200])
            return Verdict(False, f"error: {first.strip()[:300]}", ax, dt, output=out)
        if has_sorry:
            return Verdict(False, "sorry warning", ax, dt, output=out)
        return Verdict(True, "ok", ax, dt, output=out)


class BeamOracle:
    """Uses Lean Beam (https://github.com/leanprover/lean-beam): one long-lived
    `lean-beam serve` session per run; each candidate is saved and checked with
    `lean-beam sync FILE +all-diagnostics`, which waits for full elaboration."""

    def __init__(self, cfg: dict, proof_path: str, tag: str = ""):
        self.beam = cfg.get("beam_command") or "lean-beam"
        self.root = os.path.abspath(cfg.get("project_root") or os.path.dirname(proof_path))
        self.timeout = cfg_num(cfg, "timeout_seconds", 120)
        self.start_timeout = cfg_num(cfg, "beam_start_timeout_seconds", 600)
        stem = os.path.splitext(os.path.basename(proof_path))[0]
        self.work = os.path.join(os.path.dirname(os.path.abspath(proof_path)),
                                 f"{stem}_mutant_candidate{tag}.lean")
        self.rel = os.path.relpath(self.work, self.root)
        self.server: Optional[subprocess.Popen] = None
        # Each process has its own Beam session; Beam needs a private (0700)
        # session directory, which it creates itself.
        self.session_args: List[str] = []
        if tag:
            base = os.path.join(self.root, ".beam-mutate")
            os.makedirs(base, mode=0o700, exist_ok=True)
            self.session_args = ["--session-dir", os.path.join(base, tag.strip("_-") or tag)]

    def _cli(self, *args, timeout=60) -> subprocess.CompletedProcess:
        return subprocess.run([self.beam, "--root", self.root, *self.session_args, *args],
                              cwd=self.root,
                              capture_output=True, text=True, timeout=timeout,
                              start_new_session=True)

    def start(self) -> None:
        if shutil.which(self.beam) is None and not os.path.exists(self.beam):
            raise RuntimeError(f"lean-beam not found: {self.beam}")
        env = dict(os.environ, BEAM_PROGRESS="0")
        import tempfile
        self.server_err = tempfile.TemporaryFile(mode="w+")
        self.server = subprocess.Popen([self.beam, "--root", self.root,
                                        *self.session_args, "serve"],
                                       cwd=self.root, stdout=subprocess.PIPE,
                                       stderr=self.server_err, text=True, env=env,
                                       start_new_session=True)
        # `serve` prints the running-session JSON on stdout once ready
        deadline = time.monotonic() + self.start_timeout
        import selectors
        sel = selectors.DefaultSelector()
        sel.register(self.server.stdout, selectors.EVENT_READ)
        while time.monotonic() < deadline:
            if self.server.poll() is not None:
                self.server_err.seek(0)
                why = self.server_err.read().strip()[-1500:]
                self.server = None
                raise RuntimeError(f"lean-beam serve exited during start-up:\n{why}")
            if sel.select(timeout=1.0):
                line = self.server.stdout.readline()
                if line.strip().startswith("{"):
                    # keep draining stdout so the session never blocks on a full pipe
                    import threading
                    threading.Thread(target=lambda f=self.server.stdout: [None for _ in f],
                                     daemon=True).start()
                    return
        raise RuntimeError("lean-beam serve did not become ready")

    def stop(self) -> None:
        """Shut the session down the way Beam requires: ask the owner to stop and
        wait for the foreground `serve` process to exit.  Killing the owner
        first leaves the workspace fenced ("recovery required")."""
        try:
            self._cli("close", self.rel, timeout=60)
        except Exception:
            pass
        try:
            self._cli("stop", timeout=120)
        except Exception:
            pass
        if self.server:
            try:
                self.server.wait(timeout=120)
            except subprocess.TimeoutExpired:
                _kill(self.server)
                print("warning: lean-beam serve did not exit after `stop`; it was "
                      "killed. If `lean-beam doctor` reports that recovery is "
                      "required, check that no beam-daemon remains, then run "
                      "`lean-beam --root ROOT recover --generation ID`.", file=sys.stderr)
            self.server = None
        try:
            os.remove(self.work)
        except OSError:
            pass

    def check(self, source: str, timeout: Optional[float] = None) -> Verdict:
        timeout = self.timeout if timeout is None else timeout
        with open(self.work, "w", encoding="utf-8") as f:
            f.write(source)
        t0 = time.monotonic()
        try:
            cp = self._cli("sync", self.rel, "+all-diagnostics", timeout=timeout)
        except subprocess.TimeoutExpired:
            # the backend may still be elaborating: restart the session
            self.stop()
            self.start()
            return Verdict(False, f"timeout after {timeout:g}s", {},
                           time.monotonic() - t0, timed_out=True)
        dt = time.monotonic() - t0
        if cp.returncode != 0:
            return Verdict(False, f"lean-beam sync failed: {cp.stderr.strip()[:300]}",
                           {}, dt, output=cp.stdout + cp.stderr)
        try:
            res = json.loads(cp.stdout)["result"]
            errors = int(res["diagnostics"]["counts"]["error"])
            blocking = int(res.get("readiness", {}).get("blockingErrorCount", 0))
        except (ValueError, KeyError, TypeError) as e:
            return Verdict(False, f"unparsable lean-beam output ({e})", {}, dt,
                           output=cp.stdout + cp.stderr)
        # Beam prints `beam: diagnostic <severity> FILE:LINE:COL: message` with a
        # 1-based column; convert to the 0-based column the `lean` CLI uses so
        # position-based checks work the same for both oracles.
        stderr = re.sub(r"(beam: diagnostic \w+ [^\n]*?):(\d+):(\d+):",
                        lambda mm: f"{mm.group(1)}:{mm.group(2)}:{int(mm.group(3)) - 1}:",
                        cp.stderr)
        _, has_sorry, ax = parse_lean_output(stderr)
        if errors or blocking:
            first = next((l for l in cp.stderr.splitlines() if "diagnostic error" in l), "")
            return Verdict(False, f"error: {first.strip()[:300]}", ax, dt,
                           output=stderr)
        if has_sorry:
            return Verdict(False, "sorry warning", ax, dt, output=stderr)
        return Verdict(True, "ok", ax, dt, output=stderr)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def file_status(path: str) -> str:
    lines = [f"path: {path}", f"absolute: {os.path.abspath(path)}",
             f"exists: {os.path.exists(path)}"]
    if os.path.lexists(path):
        try:
            st = os.lstat(path)
            lines += [f"type: {'symlink' if stat.S_ISLNK(st.st_mode) else 'directory' if stat.S_ISDIR(st.st_mode) else 'regular file' if stat.S_ISREG(st.st_mode) else 'other'}",
                      f"mode: {stat.filemode(st.st_mode)}",
                      f"size: {st.st_size} bytes",
                      f"owner uid/gid: {st.st_uid}/{st.st_gid}",
                      f"modified: {_dt.datetime.fromtimestamp(st.st_mtime).isoformat()}",
                      f"readable by this process: {os.access(path, os.R_OK)}"]
        except OSError as e:
            lines.append(f"stat failed: {e}")
    d = os.path.dirname(os.path.abspath(path))
    lines.append(f"directory {d} exists: {os.path.isdir(d)}")
    return "\n".join(lines)


def read_proof(path: str) -> Tuple[Optional[str], Optional[str]]:
    """Return (text, None) or (None, problem)."""
    try:
        with open(path, "rb") as f:
            data = f.read()
        size = os.path.getsize(path)
    except OSError as e:
        return None, f"cannot read file: {e}"
    if len(data) != size:
        return None, f"short read: got {len(data)} of {size} bytes"
    if not data.strip():
        return None, "file is empty"
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as e:
        return None, f"file is not valid UTF-8: {e}"
    try:
        tokenize(text)
    except LexError as e:
        return None, f"file is not complete Lean source: {e}"
    return text, None


DEFAULT_STOP = {"target_accepted": 100, "max_attempts": 1000,
                "max_consecutive_failures": 200, "time_budget_seconds": 3600}


def load_config(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        cfg = json.load(f)
    if "proof_file" not in cfg:
        raise ValueError("config must contain 'proof_file'")
    base = os.path.dirname(os.path.abspath(path))
    if not os.path.isabs(cfg["proof_file"]):
        cfg["proof_file"] = os.path.join(base, cfg["proof_file"])
    given = dict(cfg.get("stopping") or {})
    for k in DEFAULT_STOP:                     # flat keys are accepted too
        if k in cfg:
            given[k] = cfg[k]
    unknown = set(given) - set(DEFAULT_STOP)
    if unknown:
        raise ValueError(f"unknown stopping condition(s): {sorted(unknown)}")
    cfg["stopping"] = {k: cfg_num(given, k, d) for k, d in DEFAULT_STOP.items()}
    if cfg.get("oracle") is None:
        cfg["oracle"] = {}
    oracle = cfg["oracle"]
    if oracle.get("kind") not in (None, "lean", "beam"):
        raise ValueError(f"oracle.kind must be 'lean' or 'beam', not {oracle['kind']!r}")
    cfg_num(oracle, "timeout_seconds", 120)          # type check now, not mid-run
    cfg_num(oracle, "beam_start_timeout_seconds", 600)
    frac = cfg_num(cfg, "statement_mutation_fraction", 0.10)
    if not 0.0 <= frac <= 1.0:
        raise ValueError("statement_mutation_fraction must be between 0 and 1")
    procs = cfg.get("max_processes")
    procs = 4 if procs is None else procs
    if not isinstance(procs, int) or isinstance(procs, bool) or procs < 1:
        raise ValueError(f"max_processes must be a positive integer, not {procs!r}")
    cfg["max_processes"] = procs
    stdout_level(cfg.get("stdout"))                 # validate now
    log_dir = cfg.get("log_dir")
    log_dir = "log" if log_dir is None else log_dir
    if not isinstance(log_dir, str) or not log_dir:
        raise ValueError(f"log_dir must be a directory path, not {log_dir!r}")
    # relative to the directory containing the proof file (the specification's
    # original location for the log)
    cfg["log_dir"] = os.path.normpath(os.path.join(
        os.path.dirname(os.path.abspath(cfg["proof_file"])), os.path.expanduser(log_dir)))
    if oracle.get("project_root") and not os.path.isabs(oracle["project_root"]):
        oracle["project_root"] = os.path.join(base, oracle["project_root"])
    return cfg


class Log:
    """JSON-lines log shared by all processes.  Every record is appended under
    a lock, so records from different processes never interleave."""

    def __init__(self, path: str, lock=None):
        self.path = path
        self.lock = lock

    def line(self, event: str, **kw) -> str:
        rec = {"time": _dt.datetime.now().isoformat(timespec="milliseconds"),
               "event": event, **kw}
        return json.dumps(rec, ensure_ascii=False) + "\n"

    def append(self, text: str) -> None:
        with open(self.path, "a", encoding="utf-8") as f:
            f.write(text)
            f.flush()

    def write(self, event: str, **kw) -> None:
        text = self.line(event, **kw)
        if self.lock is None:
            self.append(text)
        else:
            with self.lock:
                self.append(text)


def short_diff(a: str, b: str, limit: int = 40) -> str:
    d = list(difflib.unified_diff(a.splitlines(), b.splitlines(), lineterm="", n=0))[2:]
    return "\n".join(d[:limit])


STDOUT_LEVELS = ["none", "summary", "progress", "attempts", "verbose"]


def stdout_level(value) -> int:
    """Config `stdout`: a level name or number 0-4 (default "progress").
      none      nothing on stdout (errors still go to stderr)
      summary   run start, each process's stop line, final summary
      progress  + a line whenever a process's accepted count increases
      attempts  + one line per verified candidate (accepted or rejected)
      verbose   + shared mutants that did not apply, static rejections"""
    if value is None:
        return STDOUT_LEVELS.index("progress")
    if isinstance(value, int) and not isinstance(value, bool) and 0 <= value < len(STDOUT_LEVELS):
        return value
    if isinstance(value, str) and value in STDOUT_LEVELS:
        return STDOUT_LEVELS.index(value)
    raise ValueError(f"stdout must be one of {STDOUT_LEVELS} or 0-{len(STDOUT_LEVELS) - 1}, "
                     f"not {value!r}")


def say(level: int, need: str, msg: str) -> None:
    if level >= STDOUT_LEVELS.index(need):
        print(msg, flush=True)


@dataclasses.dataclass
class WorkerSpec:
    """Everything a mutation process needs (picklable)."""
    k: int                      # process number
    n: int                      # number of processes
    run_id: str
    proof_path: str
    text: str
    cfg: dict
    seed: int
    timeout: float              # per-check timeout (seconds)
    baseline_axioms: Dict[str, Tuple[str, ...]]
    deadline: float             # wall-clock end of the time budget (time.time())
    log_path: str
    out_dir: str                # where final proofs and kept candidates go
    level: int                  # stdout level


def trivial_reason(m: Mutant, cur: List[Tok], v: Verdict, trailer: str, oracle,
                   baseline_axioms, max_dead: int, deadline: float) -> Optional[str]:
    """Checks applied to a candidate Lean accepted: is it a trivial mutant?"""
    idx = {t.uid: n for n, t in enumerate(m.toks)}
    if m.touched:
        # a pure rename of binders that are never referenced
        changed = [idx[u] for u in m.touched if u in idx]
        renames = m.kind in ("subst1", "subst2", "swap_adjacent", "swap_pair")
        if renames and (pure_pattern_rename(cur, m.toks) or (changed and all(
                i in unreferenced_binders(v.output, m.toks, trailer) for i in changed))):
            return "trivial: only renames binders that are never referenced"
    if m.kind == "stmt_delete":
        return None
    # dead code: a statement containing the change can be removed and the proof
    # still verifies, so the change does not interact with the rest of the proof
    unused = unused_simp_args(v.output, m.toks, trailer)
    blocks = sorted({b for u in m.touched if u in idx
                     for b in enclosing_blocks(m.toks, idx[u])},
                    key=lambda b: b[1] - b[0])[:max_dead]
    for (bs, be) in blocks:
        left = deadline - time.time()
        if left <= 1:
            break
        probe = remove_block_and_refs(m.toks, bs, be, unused)
        pv = oracle.check(with_axiom_probes(probe, trailer),
                          timeout=min(oracle.timeout, left))
        if pv.verified and pv.axioms == baseline_axioms:
            snippet = " ".join(t.text for t in m.toks[bs:be])
            return (f"trivial: change is in dead code (removing "
                    f"'{snippet[:80]}' still verifies)")
    return None


def run_worker(spec: WorkerSpec, shared, lock, results) -> None:
    """One mutation process: its own private proof, mutator, oracle and loop.

    `shared` is the global list of accepted mutants (edit scripts).  Entries
    from other processes are high-priority candidates, each tried once.  When
    this process accepts a mutant it generated itself, it appends it."""
    cfg, k = spec.cfg, spec.k
    stop = cfg["stopping"]
    log = Log(spec.log_path, lock)
    tag = f"_w{k}" if spec.n > 1 else ""
    who = f"w{k} " if spec.n > 1 else ""
    stem = os.path.splitext(os.path.basename(spec.proof_path))[0]
    level = spec.level
    stmt_frac = cfg_num(cfg, "statement_mutation_fraction", 0.10)
    keep = bool(cfg.get("keep_candidates") or False)
    dead_check = cfg.get("reject_dead_code")
    dead_check = True if dead_check is None else bool(dead_check)
    max_dead = int(cfg_num(cfg, "max_dead_code_checks", 4))
    cand_dir = os.path.join(spec.out_dir, f"{stem}.mutants-{spec.run_id}")

    toks, trailer = tokenize(spec.text)
    oracle_cfg = cfg.get("oracle") or {}
    kind = oracle_cfg.get("kind") or "lean"
    oracle = (BeamOracle if kind == "beam" else LeanOracle)(oracle_cfg, spec.proof_path, tag)
    oracle.timeout = spec.timeout
    mut = Mutator(toks, trailer, random.Random(spec.seed), stmt_frac,
                  reject_dead_code=dead_check, uid_base=(k + 1) * 10 ** 9)
    cur, cur_text = toks, spec.text
    accepted = attempts = consecutive = static_rejects = 0
    shared_tried = shared_accepted = shared_skipped = 0
    seen, pending = 0, []
    stop_reason = None
    t0 = time.time()
    log.write("process_start", worker=k, seed=spec.seed)
    try:
        oracle.start()
        while True:
            if accepted >= stop["target_accepted"]:
                stop_reason = "target number of accepted mutants reached"
            elif attempts >= stop["max_attempts"]:
                stop_reason = "maximum number of attempts reached"
            elif consecutive >= stop["max_consecutive_failures"]:
                stop_reason = "maximum number of consecutive failures reached"
            elif time.time() >= spec.deadline:
                stop_reason = "time budget exhausted"
            if stop_reason:
                break
            # high-priority candidates: mutants accepted by other processes
            if len(shared) > seen:
                new_entries = list(shared[seen:])
                seen += len(new_entries)
                pending.extend(e for e in new_entries if e["worker"] != k)
            source, rej = "random", 0
            if pending:
                e = pending.pop(0)
                try:
                    m = mut.replay(cur, e["kind"],
                                   f"{e['description']} [shared from {e['id']}]",
                                   e["script"])
                    source = e["id"]
                    shared_tried += 1
                except Reject as why:
                    shared_skipped += 1
                    log.write("shared_skipped", worker=k, shared_id=e["id"], reason=str(why))
                    say(level, "verbose", f"{who}shared {e['id']} not applicable: {why}")
                    continue
            else:
                try:
                    m, rej = mut.propose(cur)
                    static_rejects += rej
                except Reject as why:
                    stop_reason = f"mutation space exhausted: {why}"
                    break
            attempts += 1
            mid = f"{spec.run_id}-w{k}-{attempts:06d}" if spec.n > 1 \
                else f"{spec.run_id}-{attempts:06d}"
            body = render(m.toks, trailer)
            remaining = spec.deadline - time.time()
            limit = min(oracle.timeout, max(1.0, remaining))
            v = oracle.check(with_axiom_probes(m.toks, trailer), timeout=limit)
            if v.timed_out and limit < oracle.timeout:
                log.write("attempt", worker=k, id=mid, kind=m.kind,
                          description=m.description, source=source,
                          result="abandoned", reason="time budget ran out during check")
                stop_reason = "time budget exhausted"
                break
            if v.verified and v.axioms != spec.baseline_axioms:
                v = dataclasses.replace(
                    v, verified=False,
                    reason=f"axioms changed: {v.axioms} != {spec.baseline_axioms}")
            if v.verified and dead_check:
                why = trivial_reason(m, cur, v, trailer, oracle, spec.baseline_axioms,
                                     max_dead, spec.deadline)
                if why:
                    v = dataclasses.replace(v, verified=False, reason=why)
            if keep:
                os.makedirs(cand_dir, exist_ok=True)
                with open(os.path.join(cand_dir, f"{mid}.lean"), "w", encoding="utf-8") as f:
                    f.write(body)
            entry = dict(worker=k, id=mid, kind=m.kind, description=m.description,
                         source=source, diff=short_diff(cur_text, body),
                         seconds=round(v.seconds, 3), static_rejects_before=rej)
            if v.verified:
                mut.accept(m)
                cur, cur_text = m.toks, body
                accepted += 1
                consecutive = 0
                if source == "random":
                    shared.append({"worker": k, "id": mid, "kind": m.kind,
                                   "description": m.description, "script": m.script})
                else:
                    shared_accepted += 1
                log.write("attempt", result="accepted", accepted_total=accepted, **entry)
            else:
                consecutive += 1
                log.write("attempt", result="rejected", reason=v.reason,
                          timed_out=v.timed_out, **entry)
            if rej:
                say(level, "verbose", f"{who}rejected by the rules before this mutant: {rej}")
            say(level, "attempts",
                f"{who}{mid} {'ACCEPT' if v.verified else 'reject'} "
                f"[{accepted} accepted / {attempts} attempts] {m.description}"
                + ("" if v.verified else f"  ({v.reason[:80]})"))
            if v.verified and level == STDOUT_LEVELS.index("progress"):
                print(f"process {k} (pid {os.getpid()}): accepted {accepted}, "
                      f"rejected {attempts - accepted}", flush=True)
    except KeyboardInterrupt:
        stop_reason = "interrupted"
    except Exception as e:  # noqa: BLE001 - keep the proof found so far
        import traceback
        stop_reason = f"process error: {e}"
        log.write("process_error", worker=k, error=traceback.format_exc())
    finally:
        try:
            oracle.stop()
        except Exception:  # noqa: BLE001
            pass

    suffix = f"-w{k}" if spec.n > 1 else ""
    final_path = os.path.join(spec.out_dir, f"{stem}.mutated-{spec.run_id}{suffix}.lean")
    with open(final_path, "w", encoding="utf-8") as f:
        f.write(cur_text)
    summary = dict(worker=k, reason=stop_reason, accepted=accepted, attempts=attempts,
                   consecutive_failures=consecutive, static_rejects=static_rejects,
                   shared_tried=shared_tried, shared_accepted=shared_accepted,
                   shared_not_applicable=shared_skipped,
                   seconds=round(time.time() - t0, 1), final_proof=final_path)
    # On termination each process writes its current verified proof to the log,
    # one process at a time (the log lock is held for the whole record).
    record = log.line("final_proof", proof=cur_text,
                      proof_sha256=hashlib.sha256(cur_text.encode()).hexdigest(), **summary)
    if lock is None:
        log.append(record)
    else:
        with lock:
            log.append(record)
    results[k] = summary
    say(level, "summary",
        f"process {k} (pid {os.getpid()}) stopped: {stop_reason}; accepted {accepted}, "
        f"rejected {attempts - accepted} (accepted from other processes: {shared_accepted}); "
        f"final proof {final_path}")


def main(argv: List[str]) -> int:
    if len(argv) != 2:
        print(__doc__.strip().splitlines()[2], file=sys.stderr)
        return 64
    try:
        cfg = load_config(argv[1])
    except (OSError, ValueError) as e:
        print(f"bad configuration file {argv[1]}: {e}", file=sys.stderr)
        return 64

    proof_path = os.path.abspath(cfg["proof_file"])
    stop = cfg["stopping"]
    text, problem = read_proof(proof_path)
    if text is None:
        print(f"The proof file could not be completely read: {problem}\n"
              f"File status:\n{file_status(proof_path)}", file=sys.stderr)
        return 2

    run_id = _dt.datetime.now().strftime("%Y%m%dT%H%M%S") + "-" + os.urandom(3).hex()
    stem = os.path.splitext(os.path.basename(proof_path))[0]
    level = stdout_level(cfg.get("stdout"))
    log_dir = cfg["log_dir"]
    try:
        os.makedirs(log_dir, exist_ok=True)
    except OSError as e:
        print(f"cannot create log directory {log_dir}: {e}", file=sys.stderr)
        return 64
    log = Log(os.path.join(log_dir, f"{stem}.mutate-{run_id}.log.jsonl"))
    seed = cfg.get("seed")
    if seed is None:
        seed = int.from_bytes(os.urandom(4), "big")
    nproc = cfg["max_processes"]

    toks, trailer = tokenize(text)
    oracle_cfg = cfg.get("oracle") or {}
    kind = oracle_cfg.get("kind") or "lean"
    log.write("start", run_id=run_id, seed=seed, config=cfg, proof_file=proof_path,
              proof_sha256=hashlib.sha256(text.encode()).hexdigest(), oracle=kind,
              processes=nproc)
    say(level, "summary", f"run {run_id}  seed {seed}  processes {nproc}  log {log.path}")

    t_start = time.time()
    deadline = t_start + float(stop["time_budget_seconds"])
    oracle = (BeamOracle if kind == "beam" else LeanOracle)(
        oracle_cfg, proof_path, "_base" if nproc > 1 else "")
    try:
        oracle.start()
        base = oracle.check(with_axiom_probes(toks, trailer),
                            timeout=max(oracle.timeout, 1.0) * 3)
    except Exception as e:  # noqa: BLE001
        log.write("abort", reason=f"oracle start failed: {e}")
        print(f"cannot run the Lean oracle: {e}", file=sys.stderr)
        oracle.stop()
        return 3
    oracle.stop()
    names = [d.name for d in find_decls(toks) if d.name]
    log.write("baseline", verified=base.verified, reason=base.reason,
              axioms=base.axioms, seconds=round(base.seconds, 3), theorems=names,
              unnamed_examples=sum(1 for d in find_decls(toks) if not d.name))
    missing = [n for n in names if not any(k == n or k.endswith("." + n)
                                           for k in base.axioms)]
    if not base.verified or missing:
        why = base.reason if not base.verified else f"no axiom report for {missing}"
        print(f"the original proof is not verified ({why}); stopping", file=sys.stderr)
        if base.output:
            print(base.output[-3000:], file=sys.stderr)
        log.write("stop", reason="original proof not verified", detail=why)
        return 4
    timeout = oracle.timeout
    if oracle_cfg.get("timeout_seconds") is None and cfg.get("auto_timeout", True):
        # default per-check timeout: generous multiple of the baseline time
        timeout = max(30.0, 10 * base.seconds)
    log.write("timeout", per_check_seconds=timeout)

    def spec(k: int) -> WorkerSpec:
        # process 0 uses the configured seed, so a 1-process run is reproducible
        return WorkerSpec(k, nproc, run_id, proof_path, text, cfg, seed + k, timeout,
                          base.axioms, deadline, log.path, log_dir, level)

    if nproc == 1:
        results: dict = {}
        run_worker(spec(0), [], None, results)
        summaries = [results[0]]
    else:
        import multiprocessing as mp
        ctx = mp.get_context("fork" if "fork" in mp.get_all_start_methods() else "spawn")
        with ctx.Manager() as manager:
            shared = manager.list()
            results = manager.dict()
            lock = manager.Lock()
            log.lock = lock
            procs = [ctx.Process(target=run_worker, args=(spec(k), shared, lock, results),
                                 name=f"mutate-w{k}") for k in range(nproc)]
            for p in procs:
                p.start()
            for p in procs:
                while True:
                    try:
                        p.join()
                        break
                    except KeyboardInterrupt:
                        continue      # each process stops itself and writes its proof
            summaries = [dict(results[k]) if k in results else
                         {"worker": k, "reason": f"process exited with code {procs[k].exitcode}"}
                         for k in range(nproc)]
            shared_total = len(shared)
            log.lock = None
    total = sum(s_.get("accepted", 0) for s_ in summaries)
    log.write("stop", processes=nproc, accepted_total=total,
              seconds=round(time.time() - t_start, 1), summaries=summaries,
              **({"shared_mutants": shared_total} if nproc > 1 else {}))
    if nproc > 1:
        best = max(summaries, key=lambda s_: s_.get("accepted", 0))
        say(level, "summary",
            f"all {nproc} processes stopped; accepted per process: "
            f"{[s_.get('accepted', 0) for s_ in summaries]}; "
            f"most mutated proof: {best.get('final_proof')}; log {log.path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
