# MathInfra

## Prior-art check (do this before writing any Lean for a new topic)

Before formalizing a new topic, or a major extension of an existing one, find out whether it
has already been formalized. Report what you find and wait for the user's go-ahead before
starting the proofs.

1. **Pinned Mathlib.** Search `.lake/packages/mathlib/Mathlib` for the topic's likely
   declaration names (e.g. `qBinomial`, `lucasU`, `dedekindSum`) and its key phrases, matching
   case. Also search the TODO lists in module docstrings. Broad case-insensitive patterns
   only return noise.
2. **Upstream Mathlib.** The pinned copy can lag. Check current `master` and search
   leanprover-community/mathlib4 for open and closed PRs and issues by topic name, likely
   declaration names and alternative names. `gh` is not installed; use
   `https://api.github.com/search/issues?q=repo:leanprover-community/mathlib4+<terms>`
   (unauthenticated: about 10 searches a minute). For any hit, list its declarations and
   say how far they overlap with the plan.
3. **Lean community.** Search the Lean Zulip archive and major Lean projects outside Mathlib.
4. **Other proof assistants.** Check the Isabelle Archive of Formal Proofs (isa-afp.org;
   search by topic and by textbook chapter, since many entries formalize Apostol chapter by
   chapter), plus Rocq/Coq (MathComp and similar), HOL4 and HOL Light. Open the entry's outline
   and list which of the planned theorems it contains. Don't stop at the entry's title.
5. **Alternative names.** Search the other names the literature uses for the same object
   (e.g. Gauss congruences = Dold congruences = realizable sequences; Gaussian binomials =
   q-binomials). Record them in the module docstring.

**Output:** a short table with one row per planned result: where it already exists, if
anywhere (with a link), and whether this repo would add something new (generality, a
missing theorem, Lean when only Isabelle has it). Then recommend one of: go ahead, narrow the
scope to what's missing, or build on the existing work (e.g. contribute to an open Mathlib PR
and reuse its names).

**Where the files go:** topics with no existing formalization go in `New/`; topics already
formalized anywhere (another library or an open Mathlib PR) go in `FormalizedElsewhere/`.
That applies to `MathInfra/`, `MathInfraTest/` and the `*-proofs.md` file, which sits next to
its Lean file. If prior art turns up later, move the topic and update `MathInfra.lean`,
`MathInfraTest.lean` and the README.

**If you go ahead:** add a "Prior art" section to the topic's `*-proofs.md` file and to the
README entry, citing what exists. Never write "Not in Mathlib" without the Mathlib version
or date it refers to, and mention any open PR.
