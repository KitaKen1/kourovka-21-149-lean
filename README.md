# Kourovka Notebook Problem 21.149 in Lean

> **21.149.** (V. M. Kopytov, N. Ya. Medvedev). Are there order automorphisms of Dlab groups
> that are not induced by conjugation by elements of a (possibly bigger) Dlab group?
>
> — [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46), 21st edition; proposed by
> A. V. Zenkov

This repository gives a kernel-checked Lean 4 proof of a positive answer. It has three parts.

1. **Formal Conjectures-style statement.** [`FClikeLean/21_149.lean`](FClikeLean/21_149.lean)
   states the problem in the style of
   [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures). It is an
   unofficial draft for a future Formal Conjectures pull request; Formal Conjectures does not yet
   contain Problem 21.149.
2. **Proof of that statement** on the Formal Conjectures toolchain:
   [`lean/Kourovka21149FC.lean`](lean/Kourovka21149FC.lean).
3. **Standalone proof** for Lean4Web, using mathlib only:
   [`lean4web/Kourovka21149Lean4Web.lean`](lean4web/Kourovka21149Lean4Web.lean).

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fkourovka-21-149-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FKourovka21149Lean4Web.lean)
(checked with "Latest Mathlib with Lean v4.35.0-rc3"; the file is long, so elaboration takes a
few minutes)

## The theorem

Let $`H`$ be a subgroup of the multiplicative group $`ℝ_{>0}`$ (a *slope group*). An order
automorphism is *locally right $`H`$-linear* if every point has a right neighbourhood on which the
map is affine with slope in $`H`$. The Dlab groups with slope group $`H`$ are the following
groups of locally right $`H`$-linear order automorphisms; this is the list used by Gong, Yang and
Zeng [GYZ].

| Group | Space | Condition |
|---|---|---|
| $`D_H(I)`$ | $`I=[0,1]`$ | identity near $`0`$ and near $`1`$ |
| $`D_{H*}(I)`$ | $`I`$ | identity near $`0`$ |
| $`D_{*H}(I)`$ | $`I`$ | identity near $`1`$ |
| $`\overline{D}_H(I)`$ | $`I`$ | none |
| $`D_H`$ | $`\overline{ℝ}`$ | bounded support |
| $`D_{H*}`$ | $`\overline{ℝ}`$ | support bounded below |

A Dlab group on $`I`$ carries *Dlab's order*: $`f<g`$ if $`f(x)<g(x)`$ at the first point $`x`$
where $`f`$ and $`g`$ differ.

**Theorem.** Let $`K\ne1`$ be any slope group and let $`G=D_K(I)`$ carry Dlab's order. There is an
order automorphism $`\alpha`$ of $`G`$ with the following property. Let $`H`$ be any slope group
(of any rank), let $`A`$ be any of the six Dlab groups with slope group $`H`$, and let
$`e:G\to A`$ be any injective homomorphism. Then no $`u\in A`$ satisfies
$`e(\alpha(f))=u^{-1}e(f)u`$ for all $`f\in G`$.

No order assumption is made on $`e`$ or on $`A`$. So the theorem covers the inclusions
$`D_K(I)\le D_H(I)`$ for $`K\le H`$ and the order-preserving embeddings of [GYZ].

## Formal Conjectures target

The Kourovka Notebook does not define Dlab groups. [`FClikeLean/21_149.lean`](FClikeLean/21_149.lean)
follows Dlab (1968) and [GYZ]. It defines the following:

- the six Dlab groups `IsDlabGroup`, by their membership conditions, all as subgroups of the
  order automorphisms of $`ℝ`$ (an order automorphism of $`I=[0,1]`$ is extended by the
  identity, and those of $`\overline{ℝ}`$ are those of $`ℝ`$);
- Dlab's order `DlabLt`.

It then states:

```lean
theorem kourovka_21_149 : answer(True) ↔
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧
          ∃ e : G →* A, Function.Injective e ∧ ∃ u : A, ∀ f : G, e (α f) = u⁻¹ * e f * u
```

The group $`G`$ may be any of the six Dlab groups. All six live in the order automorphisms of
$`ℝ`$, so the statement quantifies over $`G`$ once, with no case split. The last clause says that
no Dlab group $`A`$, injective homomorphism $`e : G\to A`$ and $`u\in A`$ realize $`\alpha`$ by
conjugation; it is written out in the statement rather than hidden in a definition.

The file also records the original, weaker form of the problem as the variant
`kourovka_21_149.variants.not_inner`: an order automorphism that is not inner (see the
[appendix](#appendix-history-of-the-problem)). It links to the Lean proof by Aristotle
([pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka)) and to this repository. The
reading of [GYZ] (order-preserving embeddings) is a special case of the main statement, so it is
not stated separately.

The files in `lean/` and `lean4web/` copy the definitions verbatim. They prove both statements,
`Kourovka.«21.149».kourovka_21_149` and `Kourovka.«21.149».kourovka_21_149.variants.not_inner`,
with the witness $`G=D_{\langle2\rangle}(I)`$. The variant follows from the main statement by pure
logic, and the proof files derive it this way.

The stronger statement for every nontrivial $`K`$ is proved in the same files as
`Kourovka21149.kourovka_21_149_injective`. Its line part applies to any group of locally right
$`H`$-linear order automorphisms of $`ℝ`$ that are affine near $`-\infty`$.

The development also contains the following:

- `Kourovka21149.kourovka_21_149`: an independent, shorter proof for order-preserving and
  order-reversing embeddings.
- `Kourovka21149.αo_not_inner`: the original form of the problem.
- Sanity checks:
  - `αo_induced_by_h`: $`\alpha`$ *is* induced by conjugation among all homeomorphisms.
  - `not_isDlabLikeAff_h`: the conjugating map lies in no Dlab group.
  - The six groups exist, and injective embeddings exist (the `FCTarget` section).

## Mathematical explanation (AI generated)

**The witness.** Fix $`r\in K`$ with $`r>1`$. For $`p<q`$ the *bump*
$`b_{p,q}(x)=\max\bigl(x,\ \min(p+r(x-p),\ q+r^{-1}(x-q))\bigr)`$ is the identity outside
$`[p,q]`$, has slope $`r`$ and then slope $`r^{-1}`$ on $`[p,q]`$, and moves every point of
$`(p,q)`$ to the right. Its inverse is the $`\min`$/$`\max`$ of the inverse pieces.

Let $`h:[0,1]\to[0,1]`$ be the bump on every dyadic block $`[2^{-m-2},2^{-m-1}]`$ near $`0`$ and on
every block $`[1-2^{-m-1},1-2^{-m-2}]`$ near $`1`$. Then $`h`$ fixes the points
$`X_m=2^{-m-1}\to0`$ and $`Y_m=1-2^{-m-1}\to1`$ and moves every point between two consecutive
ones. It is locally right $`K`$-linear on $`(0,1)`$ but not at $`0`$, so it lies in no Dlab
group. Conjugation $`\alpha(f)=h^{-1}fh`$ preserves $`D_K(I)`$. It also preserves Dlab's order,
because $`h`$ is increasing.

**Setting.** Extend interval automorphisms by the identity, so that every group acts on
$`ℝ`$. Suppose that $`e:G\to A`$ is injective, that $`u\in A`$ induces $`\alpha`$, and that the
elements of $`A`$ are locally right linear and affine near $`-\infty`$.

**1. Local groups are simple.** For $`0\le l_1<l_2\le1`$ let $`G_c(l_1,l_2)`$ be the elements
of $`G`$ supported in a compact subinterval of $`(l_1,l_2)`$, and let
$`Q(l_1,l_2)=[G_c,G_c]`$.

- Iterated bumps displace any compact subinterval off itself; the number of iterations comes
  from an explicit lower bound on the step size.
- Higman's identity $`[\alpha,\beta]=[[\alpha,\gamma],[\beta,\delta]]`$ shows that $`Q`$ is
  perfect.
- Every nontrivial subgroup of $`Q`$ normalised by $`Q`$ contains $`Q`$.

No infinite products are needed.

**2. First action components.** Let $`P(L)=e(Q(L))`$ and let $`K(L)`$ be the first
component of the set of points moved by $`P(L)`$. The simplicity from step 1 gives the
following.

- Every nontrivial element of $`P(L)`$ acts nontrivially on every component of the set of
  moved points. With the fact that a single element admits no infinite descending staircase of
  fixed and moved points, this shows that the first component $`K(L)`$ exists.
- $`K(L)\subseteq K(M)`$ when $`L\subseteq M`$.
- $`K(L)`$ and $`K(M)`$ are disjoint when $`L`$ and $`M`$ are disjoint. The two groups
  commute, and a perfect group acts trivially near the left end of its component. The reason
  is that right germs at a finite point are linear and germs at $`-\infty`$ are affine, so both
  germ groups are solvable.
- $`K(h^{-1}L)=u^{-1}K(L)`$, because $`u`$ induces $`\alpha`$.

**3. The staircase.** For $`0<\tau<1`$ the components $`K(0,\tau)`$ and $`K(\tau,1)`$ are
disjoint, and their left–right order does not depend on $`\tau`$.

In the orientation-preserving case put $`w(\tau)=\sup K(0,\tau)`$. It has three properties.

- $`w`$ is monotone.
- $`w`$ has no plateaus, because the component of a small interval inside $`(\beta,\gamma)`$ lies
  between $`w(\beta)`$ and $`w(\gamma)`$.
- $`w(h^{-1}\tau)=u^{-1}w(\tau)`$.

Hence $`u`$ fixes the decreasing points $`w(X_m)`$ and moves a point between each two consecutive
ones. The limit is either a fixed point where $`u`$ is right-affine, or $`-\infty`$ where $`u`$ is
affine; in both cases $`u`$ would have to be the identity nearby. This is a contradiction.

The orientation-reversing case uses $`\sup K(\tau,1)`$ and the fixed points $`Y_m`$. This is why
$`h`$ has blocks at both ends.

## Scope

- The theorem is stated for the six Dlab groups of [GYZ]. The FC round-68 report also listed
  $`D_{*H}`$ (support bounded above) and $`\overline{D}_H`$ on $`\overline{ℝ}`$. Without a condition
  at $`-\infty`$ the statement fails for this $`\alpha`$:
  - Map each block of $`(0,1)`$ affinely onto $`(-\infty,0)`$, with $`0\mapsto-\infty`$ and
    $`1\mapsto0`$.
  - Transporting $`h`$ this way gives an automorphism of $`ℝ`$ that is locally right $`K`$-linear
    at every point and whose support is bounded above.
  - It induces $`\alpha`$ through an injective, order-preserving embedding $`G\to D_H`$, for
    $`H\supseteq K\cup\{2\}`$.

  This remark is not formalized. The formalization covers any group whose elements are affine
  near $`-\infty`$.
- For $`K=1`$ the group $`D_K(I)`$ is trivial, so $`K\ne1`$ is needed.
- Compared with [GYZ] ($`K=\langle2\rangle`$, rank-one $`H`$, order-preserving embeddings, cited
  classifications of the orders of the larger group), this proof allows any $`K\ne1`$, any
  $`H`$, and any injective embedding, and uses no order classification.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `FClikeLean/` | Formal Conjectures `2424bb48…` (`v4.33.1`) | FC-style statement draft, README, pull request draft |
| `lean/` | `v4.33.1` | Proof of the FC-style statement; requires Formal Conjectures at commit `2424bb480c590237ffbb2cc831ae4cb8977e045a` |
| `lean4web/` | `v4.35.0-rc3` | Standalone mathlib-only proof for Lean4Web (mathlib `f35c415953ee34a1ad5b022fe2ed97c3c77c4093`) |

Each proof directory contains one proof file, `lakefile.toml`, `lean-toolchain` and the generated
`lake-manifest.json`.

The proof file consists of the following sections, in dependency order:

1. `Statement`: the definitions of the FC-style statement.
2. `Dlab`: Dlab groups on `[0,1]`, vendored from
   [pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka) (Apache-2.0).
3. `Basic`, `Core`, `Ext`: automorphisms of `ℝ`, the first-disagreement order, and the
   extension of interval automorphisms.
4. `Bump`, `Conj`, `Source`, `Order`: bumps, the conjugator `h`, and the automorphism `α`.
5. `Main`: the order-based proof.
6. `Affine`, `Components`, `Local`, `Higman`, `RouteI`, `MainInjective`: the proof for injective
   embeddings.
7. `Sanity`: sanity checks.
8. `FCTarget`: the bridge to the statement, and the target theorem.

## Verification

Formal Conjectures version:

```bash
cd lean
lake exe cache get
lake --wfail build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake exe cache get
lake --wfail build
```

Both builds are kernel checked and produce no warnings. The proof files contain no `sorry`,
`admit`, custom axiom, `native_decide` or `unsafe` declaration. Their final `#print axioms`
commands cover the two statements of `FClikeLean/21_149.lean` and
`Kourovka21149.kourovka_21_149_injective`. They report only Lean's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

The statement file was checked inside Formal Conjectures at the pinned commit, with its linters:

```bash
lake --wfail build 'FormalConjectures.Kourovka.«21_149»'
```

## Sources

- [The Kourovka Notebook](https://arxiv.org/abs/1401.0300v46), Problem 21.149
- [GYZ] T. Gong, Y. Yang and M. R. Zeng, *An order automorphism of a Dlab group not induced by
  conjugation*, [arXiv:2609.18630](https://arxiv.org/abs/2609.18630)
- [vDJMM] W. van Doorn, E. Judin, P. Monticone and D. Morrison, *On some problems from the
  Kourovka Notebook*, [arXiv:2607.17477](https://arxiv.org/abs/2607.17477), Appendix A (history of
  the problem statement)
- V. Dlab, *On a family of simple ordered groups*, J. Austral. Math. Soc. 8 (1968), 591–608
- G. Higman, *On infinite simple permutation groups*, Publ. Math. Debrecen 3 (1954), 221–226
- [pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka): Lean definitions of Dlab
  groups and the solution of the original problem
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

The proof strategy, the Lean formalization and the repository packaging were developed with
assistance from Anthropic's Claude (Claude Code), under the direction of KitaKen1 (Kenta
Kitamura).

## Appendix: history of the problem

### Timeline

| When | Stage | Question | What happened | Source |
|---|---|---|---|---|
| Jan 2026 | **Posed** | original | *"Are there order automorphisms of Dlab groups that are not inner automorphisms?"* Posed by A. V. Zenkov; due to V. M. Kopytov and N. Ya. Medvedev. | [Kourovka v40](https://arxiv.org/abs/1401.0300v40)–[v43](https://arxiv.org/abs/1401.0300v43) |
| by Jun 2026 | **Solved** | original | Aristotle (Harmonic) answers *yes*, with a Lean proof. The solution is sent to the editors. | [vDJMM], Appendix A; [pitmonticone/Kourovka](https://github.com/pitmonticone/Kourovka) |
| Jun 2026 | **Revised** | revised | A problem author confirms the solution but says he meant a stronger question: *"… not induced by conjugation by elements of a (possibly bigger) Dlab group?"* | [Kourovka v44](https://arxiv.org/abs/1401.0300v44); [vDJMM], Appendix A |
| Sep 2026 | **Partially solved** | revised | Gong–Yang–Zeng answer *yes* for rank-one slope groups and order-preserving embeddings. | [GYZ] |
| Sep 2026 | **Fully solved** | revised | This repository answers *yes* for every slope group and every injective embedding, with a kernel-checked proof. | this repository |

### What each solution covers

| | Aristotle (Harmonic) | Gong–Yang–Zeng [GYZ] | This repository |
|---|---|---|---|
| Question | original: not inner | revised: not induced | revised: not induced |
| Group $`G`$ | $`D_{\langle2\rangle}(I)`$ | $`D_{\langle2\rangle}(I)`$, either Dlab order | $`D_K(I)`$, every $`K\ne1`$ |
| Bigger group $`A`$ | $`G`$ itself | the six Dlab groups, rank-one $`H`$ | the six Dlab groups, every $`H`$ |
| Embedding $`G\to A`$ | identity | order-preserving | every injective homomorphism |
| Conjugating map | two linear pieces (slopes $`2`$, $`1/2`$) | breakpoints accumulating at $`0`$ | breakpoints accumulating at $`0`$ and $`1`$ |
| Key input | only the identity is fixed by the automorphism | classification of the orders of $`A`$ | Higman simplicity, action components, staircase |
| Proof | Lean | informal | Lean (kernel-checked) |
| Statement in [`FClikeLean/21_149.lean`](FClikeLean/21_149.lean) | `variants.not_inner` | special case of `kourovka_21_149` | `kourovka_21_149` |

### Notes

- **Why the original solution does not answer the revised question.** Aristotle's conjugating map
  is locally right $`\langle2\rangle`$-linear at every point. So it lies in the bigger Dlab group
  $`\overline{D}_{\langle2\rangle}(I)`$, and there the automorphism *is* induced by conjugation.
  A witness for the revised question needs a conjugating map outside every Dlab group, for
  example one whose breakpoints accumulate at an endpoint.
- **Why GYZ need rank one.** Their proof identifies the embedded group through the known
  classifications of the orders of the bigger group (Dlab 1968, Zenkov–Medvedev 1999,
  Medvedev 2001). These classifications need a rank-one slope group.
- **Why this repository needs neither.** The proof works for arbitrary injective homomorphisms. It
  uses only the dynamics of the image: simplicity of local commutator groups, first action
  components, and a staircase along the fixed points of $`h`$. The blocks at both ends of
  $`[0,1]`$ handle the two possible orientations.
- **Outside the six groups.** The two further groups on $`\overline{ℝ}`$ are discussed under
  [Scope](#scope).
