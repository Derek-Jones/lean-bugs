# mutate_lean.py

Accumulates as many small modifications ("mutants") as possible in a Lean 4
proof while the proof stays *verified*, following `mutate-lean.txt`.

```
python3 mutate_lean.py config.json
```

Python 3.9+, no third-party packages. Needs a Lean 4 toolchain (`lean`, or
`lake env lean` inside a Lake project), or an installed Lean Beam.

## Configuration

```json
{
  "proof_file": "Sample.lean",
  "max_processes": 4,
  "log_dir": "log",
  "stdout": "progress",
  "stopping": {
    "target_accepted": 25,
    "max_attempts": 300,
    "max_consecutive_failures": 60,
    "time_budget_seconds": 1800
  },
  "oracle": {
    "kind": "lean",
    "lean_command": ["lean"],
    "project_root": null,
    "timeout_seconds": null
  },
  "statement_mutation_fraction": 0.1,
  "seed": 7,
  "keep_candidates": false
}
```

| Key | Meaning |
| --- | --- |
| `proof_file` | Lean file to mutate (relative paths are relative to the config file). Required. |
| `max_processes` | Number of mutation processes run concurrently (default 4; 1 = the original single-process behaviour). See "Multiple processes". |
| `log_dir` | Directory for the log file and the run's other outputs (final mutated proofs, kept candidates). Default `"log"`. A relative path is relative to the directory containing the proof file; the directory is created if needed. |
| `stdout` | How much is printed to stdout (default `"progress"`; a name or 0-4): `none` nothing; `summary` the run line, each process's stop line and the final summary; `progress` adds a line `process K (pid P): accepted A, rejected R` each time a process's accepted count increases; `attempts` adds one line per verified candidate; `verbose` adds shared mutants that did not apply and rule-rejection counts. Errors always go to stderr. |
| `stopping.*` | The four stopping conditions. They may also be given as top-level keys. Missing ones default to 100 / 1000 / 200 / 3600. Target, attempts and consecutive failures apply to each process; the time budget is one wall-clock budget for the whole run. |
| `oracle.kind` | `"lean"` (default): runs `lean_command FILE`. `"beam"`: runs a Lean Beam session (`lean-beam serve`, then `lean-beam sync FILE +all-diagnostics` per candidate). |
| `oracle.lean_command` | Command list, e.g. `["lean"]` or `["lake", "env", "lean"]` for a Lake project. |
| `oracle.project_root` | Working directory for Lean / root for Beam. Default: the proof's directory. |
| `oracle.timeout_seconds` | Per-check timeout. `null` = max(30 s, 10 × the time to check the original). |
| `oracle.beam_command` | Path to `lean-beam` (Beam only). |
| `statement_mutation_fraction` | Share of mutants that change a complete statement (spec: 10%). |
| `seed` | Random seed. Process *k* uses `seed + k`, so a 1-process run is reproducible. `null` = random (the seed is logged). |
| `keep_candidates` | Save every candidate proof, named by its unique id, in `<log_dir>/<stem>.mutants-<run>/`. |
| `reject_dead_code` | Default `true`: run the dead-code and rename checks described below (extra Lean runs, only for candidates that verify). |
| `max_dead_code_checks` | Most statement removals tried per verified candidate (default 4). |

Examples in `examples/`: `config.json` for the AIME 2020 II P6 proof
(`aimeII_2020_p6.lean`, needs a Lake project with Mathlib: set
`project_root`), and `config-sample.json` for `Sample.lean` (core Lean only).
`CoreCycle.lean` is a second core-Lean test proof in the style of the AIME one,
and `config-beam.json` runs it through Lean Beam (the proof's directory must be
a Lake project, i.e. contain `lean-toolchain` and a lakefile).

### Using Lean Beam

With `"kind": "beam"` the program starts its own `lean-beam --root ROOT serve`
session, checks each candidate with `lean-beam sync FILE +all-diagnostics`
(error count from the JSON result; warnings and `#print axioms` output from the
streamed diagnostics), and shuts the session down with `lean-beam stop`. A
timed-out check restarts the session. Do not run another Beam session on the
same project at the same time.

If the program is killed abruptly, Beam may report "recovery required" for the
project. Check that no `beam-daemon` process remains, then run the
`lean-beam --root ROOT recover --generation ID` command printed by
`lean-beam doctor`.

Beam is installed from a checkout with `./scripts/install-beam.sh` (needs
`elan`). For a locally built Lean, link it into elan and install for that
link, as in Beam's `docs/CUSTOM_TOOLCHAINS.md`:

```
elan toolchain link lean4-dev /path/to/lean4/build/release/stage1
./scripts/install-beam.sh --custom-toolchain lean4-dev
echo lean4-dev > lean-toolchain     # in the project
```

## Multiple processes

With `max_processes` = N (default 4), the original proof is checked once, then N
processes run concurrently. Each behaves exactly like the single-process
program: it has its own private copy of the proof, random generator, Lean
oracle and candidate file (`<stem>_mutant_candidate_w<k>.lean`; with Beam, its
own session under `<project>/.beam-mutate/w<k>`). Each process repeatedly mutates
and verifies its own proof, applying all the rules below.

**Sharing.** When a process accepts a mutant it generated itself, it adds it
to a global list shared by all processes. Before drawing a new random mutant,
every process takes the next shared entry from another process that it has
not tried yet; it tries each entry once, with the same checks as any other
mutant. A shared mutant is stored as an edit script that refers to tokens by
identity (e.g. "substitute token #57 `rw` → `simp`", "insert `←` before token
#80"). Tokens of the original proof have the same identity in every process.
If a process's proof has diverged so that the anchored tokens are gone or
differ, or applying the edit would break a rule there (for example reversing
an earlier change), the entry is skipped without calling Lean
(`shared_skipped` in the log). Shared mutants that a process accepts are not
shared again.

**Termination.** Each process stops on its own stopping conditions (or when
the common time budget runs out, or on Ctrl-C). Then, holding the log's lock
so that processes write one at a time, it writes its current verified proof
to the log (`final_proof` record) and to `<log_dir>/<stem>.mutated-<run>-w<k>.lean`.
The program ends when all processes have stopped; the closing `stop` record
lists every process's summary.

Each process runs its own Lean (or Beam session), so memory use grows with
N. With Mathlib imports, allow several GB per process.

## What happens

1. The proof file is read in full (bytes = file size, valid UTF-8, no
   unterminated comment/string). Otherwise the file status (existence, type,
   permissions, size, owner, mtime, readability) is printed and the program
   exits with status 2.
2. The original is checked. "Verified" = no errors, no
   `declaration uses 'sorry'` warning, and the `#print axioms` result of every
   named theorem/lemma. The program adds `#print axioms NAME` after each
   theorem in the checked copy only; the proof file itself is never modified.
   If the original is not verified the run stops (status 4).
3. Loop: pick a mutant at random, reject it statically if it breaks a rule
   (below), otherwise write the candidate to `<stem>_mutant_candidate.lean`
   beside the proof and verify it. If still verified with the original axioms,
   the mutant is kept and the next mutant is added on top; otherwise it is
   discarded. Timeouts count as failures.
4. Stop on whichever condition is met first. The final proof is written to
   `<log_dir>/<stem>.mutated-<run>.lean`.

Every candidate sent to Lean has a unique id `<run-id>-<attempt number>`.

### Mutant operators

Only tokens inside the proof bodies of `theorem`/`lemma`/`example` (after the
top-level `:=`) are changed.

Token level (one or two tokens): substitute a binary operator by another
(70% the same family, e.g. `≤`→`<`), an identifier by another identifier
used in the file (tactic names are swapped for tactic names, terms for terms),
a numeral by a nearby numeral; substitute two nearby tokens; delete one or two
adjacent tokens; insert one token or a two-token sequence taken from the proof;
swap two adjacent tokens; swap two nearby tokens of the same class.

Statement level (`statement_mutation_fraction`): delete, duplicate, swap with
the next statement at the same indentation, or replace with another statement
of the proof.

### Rules enforced before Lean is called

* Theorem statements: the tokens from each declaration's start to its `:=`
  must be unchanged, and the set of declarations must be the same.
* No new `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`,
  `set_option`, `csimp`, `unsafe`, `opaque`, `extern`, `ofReduceBool`,
  `macro`, `notation`, `syntax`, `instance`, `@[`, `#command`, or any other
  declaration/command keyword (counted against the original).
* Comment/whitespace-only changes are impossible: comments are trivia in the
  lexer and are never mutated; a candidate must change the token sequence.
* Trivial mutants (static part): candidates introducing `skip`, `done`,
  `trace_state`, `trace`, `checkpoint`, `sleep` etc. are rejected.
* No reversal: a candidate is rejected if it returns the proof to any earlier
  state (indirect reversal), gives a token a value it held before, deletes a
  token or statement inserted by an earlier mutant, re-inserts deleted text at
  the same place, or swaps a pair that was swapped before.

### Trivial-mutant checks after Lean accepts a candidate

The specification excludes changes "whose result does not interact with other
proof statements". A candidate that verifies is therefore checked further
(`reject_dead_code`):

* **Dead code.** The statement containing the change is removed, then each
  enclosing statement (a statement plus its more-indented children), innermost
  first. If any removal still verifies with the original axioms, the change was
  in code nothing depends on, and the candidate is rejected. When the removed
  statement is `have NAME`, uses of `NAME` that Lean reports as unused simp
  arguments are removed too, so a hypothesis that is named in a `simp [...]`
  list but not needed still counts as dead. Typical catches: edits inside an
  unused `have`, and edits to `<;> tac` steps that run after the goal is
  already closed (common in machine-generated proofs such as the AIME example).
* **Pure renames.** Substitutions/swaps that only rename binders that are never
  referenced: either reported by Lean's unused-variable linter, or variables of
  a `| ctor a b =>` alternative that the alternative never mentions (the linter
  does not report those).

Deleting a whole statement is not subject to the dead-code check, so removing
a redundant statement counts as a mutant. Duplicating a statement is disabled
while the check is on, because a duplicate that verifies is always removable.

## Log

`<log_dir>/<stem>.mutate-<run-id>.log.jsonl` (by default `log/` beside the
proof), one JSON object
per line, shared by all processes (each record is written under a lock):

* `start` (config, seed, number of processes, proof hash), `baseline` (axioms
  per theorem), `timeout`;
* `process_start` (process number, seed);
* one `attempt` per candidate: process, id (`<run>-w<k>-<n>`), operator,
  description, `source` (`random`, or the id of the shared mutant it came
  from), unified diff against that process's current proof, seconds,
  accepted/rejected and reason;
* `shared_skipped`: a shared mutant that does not apply to this process's
  proof;
* `final_proof`, one per process, written one at a time at termination: the
  complete proof text, its hash, and the process's summary (stop reason,
  accepted, attempts, shared mutants tried/accepted/not applicable);
* `stop`: all summaries and the total number of accepted mutants.

## Testing done

Against Lean v4.36.0-rc1 built from source, and Lean Beam built from its
GitHub checkout for that Lean (this sandbox has no network route to Lean or
Mathlib binaries):

* `CoreCycle.lean`, 1 process, 400 attempts with `lean`: before the
  trivial-mutant checks 17 mutants were accepted, several of them edits to an
  unused `have`; with the checks, every accepted mutant changes code the proof
  depends on. The edit-script refactor for sharing reproduces the
  single-process run exactly (same seed, same result).
* `CoreCycle.lean`, 4 processes, 150 attempts each: mutants accepted by one
  process were tried and accepted by the others within a few attempts; each
  process ended with 4-5 accepted mutants. All four final proofs re-verify
  independently with the original axioms; every log line is valid JSON; each
  `final_proof` record matches its file.
* Replay of shared mutants on diverged proofs: skipped when the anchored
  tokens are gone, applied when the proof diverged elsewhere, and rejected
  when it would reverse the receiving process's own change.
* Ctrl-C during a 4-process run: every process stops within a second and
  writes its proof to the log; no Lean processes or candidate files remain.
* Beam oracle, 1 and 4 processes: the same seed gives the same accept/reject
  sequence as `lean`; each process has its own Beam session, and every session
  ends shut down (`lean-beam doctor`: absent; no `beam-daemon` left).
  Timeouts restart the session. Beam's 1-based columns are converted to the
  CLI's 0-based ones.
* Timeouts with `lean`: counted as failures, and the process group is killed.
* Stopping conditions, config validation, and unreadable proof files.
* `log_dir`: default `log/` beside the proof, and a nested absolute path, are
  created; invalid values are rejected. `stdout`: each of the five levels, with
  1 and 4 processes; invalid levels are rejected.
* `aimeII_2020_p6.lean`: lexing round-trips exactly, the theorem statement
  (lines 9-11) is protected, and the 228 statements are found. It was **not**
  checked by Lean here, because Mathlib's prebuilt cache is blocked in this
  sandbox.

## Outstanding issues

1. **Mathlib proofs not run here.** The AIME example needs a Lake project with
   Mathlib (`lake exe cache get`), which this sandbox cannot download. The code
   path is the same as for core Lean (`lake env lean FILE`). Expect a few
   seconds per check just to import Mathlib, plus elaboration time; the
   proof's many `norm_num`/`simp_all` calls may take much longer.
2. **Beam was tested with a stand-in for `elan`.** Real `elan` could not be
   built here (the Rust crate registry is blocked), so a small script mapping
   toolchain names to the local Lean build was used for the install. Beam was
   tested on core Lean only, and only through its CLI (not its MCP server).
3. **`example` has no name**, so `#print axioms` cannot be run on it: for
   examples, "verified" means only no errors and no sorry.
4. **Trivial-mutant detection is heuristic.** The dead-code check misses a
   change to a statement that is needed only because a later statement names
   it in a way Lean does not flag (e.g. an unneeded hypothesis passed to
   `exact`/`apply` arguments that tolerate it). Pure renames are only detected
   for linter-reported binders and `|` pattern alternatives (not, e.g.,
   `fun x =>` where the body ignores `x` and Lean does not warn).
5. **Cost.** Each candidate that verifies gets up to `max_dead_code_checks`
   extra Lean runs.
6. **"Indirect reversal" is an interpretation**: a candidate is rejected if it
   returns the proof to any earlier state, gives a token a value it held before,
   deletes a token or statement inserted by an earlier mutant, re-inserts
   deleted text at the same place, or repeats an earlier swap. Confirm this
   matches the intent.
7. **Only theorem/lemma/example proof bodies are mutated**; `def` bodies are
   left alone because changing them could change what a theorem states.
8. **Statements are found from layout** (line start or after `by`/`·`/`=>`,
   bracket depth 0). Unusual formatting can split statements oddly; this costs
   failed attempts or missed dead-code detections, never acceptance of a proof
   Lean rejects.
9. **Deleting or replacing a statement drops comments inside it** (a side
   effect, not a counted mutant).
10. **With `"kind": "lean"`, one fresh `lean` process per candidate.** That is
    slow for files with heavy imports such as Mathlib; use the Beam oracle.
11. **"Control Agent"** in the specification is taken to be this program.
12. **Stopping conditions with several processes are an interpretation.**
    Target, maximum attempts and maximum consecutive failures apply to each
    process (so a run can make up to N × `max_attempts` Lean checks); the time
    budget is shared. A shared mutant that applies counts as an attempt for the
    process that tries it.
13. **Shared mutants are anchored to token identity**, so a mutant whose
    tokens were changed or removed in the receiving process is skipped rather
    than adapted. Mutants that were themselves received are not re-shared, and
    a process that stops early does not see later shared mutants.
14. **Processes compete for CPU and memory.** On this 2-core sandbox 4
    processes ran about twice as fast in total as 1; beyond the core count
    there is no gain, and each Lean/Beam instance needs its own memory.
