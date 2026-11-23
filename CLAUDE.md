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

## vibe-research and `MathApplied`

<https://github.com/rabidlorax/vibe-research> holds AI-conducted research projects in many
fields, laid out as `domains/<domain>/projects/<project-slug>/`. It contains no Lean code:
every proof a project depends on is formalized here. A project there points to a theorem
here by its **Lean declaration name**, the **commit hash** of this repo at which it was
checked, and the **axioms** it depends on (from the topic's `Axioms` test file). It does not
use file paths.

### Renaming and deleting

Before renaming or deleting any public declaration, check whether vibe-research points to
it: clone that repo (`git clone --depth 1 https://github.com/rabidlorax/vibe-research`) and
search it for the name with `grep -rnwF`. If it does, either keep the old name as a
deprecated alias (`@[deprecated newName (since := "YYYY-MM-DD")] alias oldName := newName`)
or report to the user which pointers in vibe-research need updating. Do the same before
changing a cited theorem's statement or its axioms. Moving a file between folders without
renaming declarations is safe.

### Where a proof goes

- **General mathematics** goes in `MathInfra/New/` or `MathInfra/FormalizedElsewhere/`, as
  above.
- **A proof specific to one vibe-research project** goes in
  `MathApplied/<Domain>/<Project>/<Topic>.lean`, where `<Domain>` and `<Project>` are the
  CamelCase forms of the vibe-research domain and project slug
  (`domains/economics-and-social-science/projects/stable-matching-bound` becomes
  `MathApplied/EconomicsAndSocialScience/StableMatchingBound/`). Keep the four-file
  convention: the Lean file, `<Topic>-proofs.md` beside it, and
  `MathAppliedTest/<Domain>/<Project>/<Topic>.lean` and `<Topic>Axioms.lean`. Add the imports
  to `MathApplied.lean` and `MathAppliedTest.lean`. Declarations are in the root namespace,
  as in `MathInfra`, so a name must not clash with one in another project or in `MathInfra`.
- `MathApplied` may import `MathInfra`. `MathInfra` must never import `MathApplied`.
- If a result turns out to be general, put it in `MathInfra`, not `MathApplied`, and import
  it from there.
- Do not create a domain or project folder before it has a topic.

The prior-art check applies to `MathApplied` topics as it does to `MathInfra` topics.
`MathApplied` has no `New/` / `FormalizedElsewhere/` split; record the prior art in the
"Prior art" section of the topic's `-proofs.md` file.

### Conjectures

State a conjecture without proof as a definition of a proposition:

```lean
/-- Docstring: the statement in words, its source, and its status with a date. -/
def fooConjecture : Prop := ...
```

Never state one as a `theorem` with `sorry`, and never as an `axiom`: the README's guarantee
that a warning-free build means everything is checked must stay true.

- General conjectures go in `MathInfra/Conjectures/<Topic>.lean`; a conjecture belonging to
  one vibe-research project goes in that project's folder under `MathApplied/`.
- A result proved assuming a conjecture takes it as an explicit hypothesis.
- If a conjecture is later proved, replace the `def` with the theorem and move the file
  according to the normal rules. That removes a public declaration, so the renaming rule
  above applies.
- The prior-art check for a conjecture includes
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

### Computations done outside Lean

For a result that rests on a large search or computation run in other code (Python, C, a SAT
solver):

- The search code and the certificate it outputs go in a folder `<Topic>-search/` next to
  `<Topic>.lean`, which checks the certificate. It does not redo the search.
- `<Topic>-proofs.md` states exactly what Lean verified and what is trusted, and gives the
  command that regenerates the certificate.
- `native_decide` is allowed. The `Axioms` test file will then show the extra axiom, and
  `<Topic>-proofs.md` must say that the result trusts the Lean compiler.
- If no certificate is checked in Lean at all, the result is not a theorem of this repo.
  State it as a conjecture and describe the computation in its docstring.

Do not build shared tooling for this until a topic needs it.
