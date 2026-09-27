# Prospective Formal Conjectures statement

This directory contains an **unofficial, AI-assisted draft** of Problem 21.149 of
[the Kourovka Notebook](https://arxiv.org/abs/1401.0300v46), written in the style used by
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

It is not an official Formal Conjectures file. It has not been submitted, reviewed, approved or
merged. At the pinned upstream commit
[`2424bb48`](https://github.com/google-deepmind/formal-conjectures/tree/2424bb480c590237ffbb2cc831ae4cb8977e045a/FormalConjectures/Kourovka)
there is no `FormalConjectures/Kourovka/21_149.lean`.

## Files

- [`21_149.lean`](21_149.lean) is the file to add as `FormalConjectures/Kourovka/21_149.lean`.
  It contains two statements, both marked `research solved` with `answer(True)`:

  | Declaration | Content | `formal_proof` links |
  |---|---|---|
  | `kourovka_21_149` | the current problem (Kourovka v46) | this repository, lines 5740–5775 |
  | `kourovka_21_149.variants.not_inner` | the original problem (Kourovka v43): not inner | [pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka) (Aristotle), and this repository, lines 5777–5786 |

  The line numbers refer to [`../lean/Kourovka21149FC.lean`](../lean/Kourovka21149FC.lean).
  Replace `COMMIT` with the commit hash of this repository after it is published.
- [`PR_DRAFT.md`](PR_DRAFT.md) is a draft of the pull request title and description.

The `by sorry` proofs in `21_149.lean` are intentional: Formal Conjectures is a statement
repository, and its linter requires a statement with a `formal_proof` link to be proved exactly
`by sorry`.

## Relationship to the proofs

- [`../lean/Kourovka21149FC.lean`](../lean/Kourovka21149FC.lean) imports `FormalConjecturesUtil`
  at the same commit. It copies the definitions of `21_149.lean` verbatim and proves both
  statements under the same names, with the real `answer( )` elaborator.
- [`../lean4web/Kourovka21149Lean4Web.lean`](../lean4web/Kourovka21149Lean4Web.lean) does the
  same with mathlib only, using a local `answer( )` notation with the same kernel term.

In both builds, `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for both
statements.

The theorem `kourovka_21_149` of
[pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_21_149.lean#L770-L775)
implies `variants.not_inner`. It uses the same `Dlab` definitions (`DlabGroup H`), and it states
that some order automorphism of `DlabGroup H` for its first-disagreement order
(`IsDlabBiOrder`) is not inner.

## Formalisation choices

- **The six Dlab groups.** The larger group $`A`$ ranges over $`D_H(I)`$, $`D_{H*}(I)`$,
  $`D_{*H}(I)`$ and $`\overline{D}_H(I)`$ on $`I=[0,1]`$, and over $`D_H`$ and $`D_{H*}`$ on
  $`\overline{ℝ}`$. This is the list in Gong–Yang–Zeng
  ([arXiv:2609.18630](https://arxiv.org/abs/2609.18630)).
  - The groups are defined by their membership conditions, so the statement file needs no
    closure proofs. The proof files show that all six groups exist as subgroups.
  - The group $`D_{*H}`$ on $`\overline{ℝ}`$ (support bounded above) is not included; GYZ also
    exclude it. Without a condition at $`-\infty`$, the witness below is induced by conjugation
    in that group: transport the conjugating map $`h`$ to $`(-\infty,0)`$ by a piecewise-linear
    map sending $`0\mapsto-\infty`$ and $`1\mapsto0`$.
- **Where the definitions come from.** The Notebook does not define Dlab groups. The file follows
  Dlab (1968) and GYZ: four Dlab groups act on $`I=[0,1]`$ and two on $`\overline{ℝ}`$.
- **The group $`G`$.** $`G`$ is any of the six Dlab groups, with an arbitrary slope group $`K`$.
  All six are subgroups of the order automorphisms of $`ℝ`$: an order automorphism of $`I`$ is
  extended by the identity (it fixes every point outside $`(0,1)`$), and those of
  $`\overline{ℝ}`$ are those of $`ℝ`$. Each statement starts with
  `∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧ …`. The extension is an
  isomorphism onto its image that preserves Dlab's order; the proof file checks this. The proofs
  use $`G=D_{\langle2\rangle}(I)`$, extended to $`ℝ`$.
- **Dlab's order.** `DlabLt` is defined for elements of any group of order automorphisms of
  $`ℝ`$. On extended maps of $`I`$ it is the first-disagreement order used by
  [pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka) for the original problem.
  An order automorphism is a group automorphism $`\alpha`$ with
  `DlabLt (α f) (α g) ↔ DlabLt f g`.
- **"Induced by conjugation".** The main statement ends with
  `¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧ ∃ e : G →* A, …`:
  no Dlab group $`A`$, injective homomorphism $`e : G \to A`$ and $`u\in A`$ satisfy
  $`e(\alpha(f))=u^{-1}e(f)u`$ for all $`f`$. This matches "not induced" in the problem. The
  clause is written out in the statement, not hidden in a definition.
- **"Possibly bigger".** The larger group $`A`$ contains $`G`$ through an injective homomorphism
  $`e`$, and $`\alpha`$ is induced by $`u\in A`$ when $`e(\alpha(f))=u^{-1}e(f)u`$ for all $`f`$.
  Every injective homomorphism is allowed. This includes the inclusions $`G\le A`$ and the
  order-preserving embeddings of GYZ.
- **Slope groups.** Slope groups are arbitrary subgroups of `NNRealˣ` (positive reals), of any
  rank.
- **Variant.** `not_inner` follows from the main statement by pure logic, and the proof files
  derive it this way: an inner automorphism is induced in the Dlab group $`A=G`$, with
  $`e=\mathrm{id}`$. The reading of GYZ (order-preserving embeddings, proved there for rank-one
  $`H`$) is a special case of the main statement, so it is not stated separately.
- **Boundary cases.** A trivial group $`G`$ (for example $`K=1`$) is not a witness: its only
  automorphism is the identity, which is induced ($`A=G`$, $`e=\mathrm{id}`$, $`u=1`$). So the
  statement is not satisfied vacuously.

## How it was checked

The file was copied to `FormalConjectures/Kourovka/21_149.lean` inside Formal Conjectures at
commit `2424bb48`. Then

```bash
lake --wfail build 'FormalConjectures.Kourovka.«21_149»'
```

succeeds with the Formal Conjectures linters enabled. Removing the theorem docstring or the
`AMS` tag makes this build fail, so the linters are active.

## AI usage disclosure

This statement draft and its packaging were developed with assistance from Anthropic's Claude
(Claude Code), under the direction of KitaKen1 (Kenta Kitamura).
