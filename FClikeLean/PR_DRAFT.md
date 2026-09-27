# Pull request draft

Before opening the pull request:

1. Publish this repository as `KitaKen1/kourovka-21-149-lean`, or change the links below and in
   `21_149.lean` to the actual name.
2. Replace `COMMIT` with the published commit hash, here and in `21_149.lean`.
3. Copy `21_149.lean` to `FormalConjectures/Kourovka/21_149.lean` in a fork of Formal
   Conjectures and run `lake --wfail build 'FormalConjectures.Kourovka.«21_149»'`.
4. Sign the Google CLA if needed. Optionally open an issue first, as
   [CONTRIBUTING.md](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md)
   suggests.

---

**Title:** Formalize Kourovka Problem 21.149 and mark it as solved

This PR adds Kourovka Notebook Problem 21.149 with one variant. Both statements are marked as
solved with `answer(True)` and link kernel-checked Lean 4 proofs.

- `kourovka_21_149`: the current wording
  ([v46](https://arxiv.org/abs/1401.0300v46)).
  > Are there order automorphisms of Dlab groups that are not induced by conjugation by
  > elements of a (possibly bigger) Dlab group?
- `kourovka_21_149.variants.not_inner`: the original wording
  ([v43](https://arxiv.org/abs/1401.0300v43)), which asked for an order automorphism that is
  not inner. Aristotle (Harmonic) solved it, and the problem was then revised
  ([arXiv:2607.17477](https://arxiv.org/abs/2607.17477), Appendix A).

Gong–Yang–Zeng ([arXiv:2609.18630](https://arxiv.org/abs/2609.18630)) answered the current
wording for order-preserving embeddings and rank-one slope groups. Their reading is a special case
of the main statement, so it is not stated separately.

The Notebook does not define Dlab groups. The file follows Dlab (1968) and Gong–Yang–Zeng: the
six Dlab groups $D_H(I)$, $D_{H*}(I)$, $D_{*H}(I)$, $\overline{D}_H(I)$, $D_H$ and $D_{H*}$. In
the main statement:

- $G$ is any of the six Dlab groups (`IsDlabGroup`), with Dlab's first-disagreement order.
  All six are subgroups of the order automorphisms of $\mathbb{R}$: an order automorphism of
  $[0,1]$ is identified with its extension by the identity, and the order automorphisms of
  $\overline{\mathbb{R}}$ are those of $\mathbb{R}$.
- The bigger group is also any of the six, and contains $G$ through an injective homomorphism.
- Slope groups are arbitrary.

The main statement is below. Its last clause says that no Dlab group $A$, injective
homomorphism $e : G \to A$ and $u \in A$ realize $\alpha$ by conjugation:

```lean
theorem kourovka_21_149 : answer(True) ↔
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧
          ∃ e : G →* A, Function.Injective e ∧ ∃ u : A, ∀ f : G, e (α f) = u⁻¹ * e f * u
```

Proofs:

- `kourovka_21_149`: https://github.com/KitaKen1/kourovka-21-149-lean/blob/COMMIT/lean/Kourovka21149FC.lean#L5740-L5775
- `kourovka_21_149.variants.not_inner`:
  https://github.com/pitmonticone/Kourovka/blob/dcfdbdad8c434e30f6151fb3b4343364d70eeed4/Kourovka/Problem_21_149.lean#L770-L775
  and https://github.com/KitaKen1/kourovka-21-149-lean/blob/COMMIT/lean/Kourovka21149FC.lean#L5777-L5786

Repository: https://github.com/KitaKen1/kourovka-21-149-lean

Lean4Web: https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fkourovka-21-149-lean%2FCOMMIT%2Flean4web%2FKourovka21149Lean4Web.lean

The proof file imports `FormalConjecturesUtil` at commit `2424bb48` and copies the definitions of
this file verbatim. For both statements, `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`.

Formalisation notes:

- **The six groups.** These are the six groups of GYZ. $D_{*H}$ on $\overline{\mathbb{R}}$
  (support bounded above) is not included. Without a condition at $-\infty$, the conjugation used
  in the proof can be realised in that group.
- **Embeddings.** Allowing every injective homomorphism covers the inclusions and the
  order-preserving embeddings of GYZ.
- **Variant.** `variants.not_inner` follows from the main statement by pure logic ($A = G$,
  $e = \mathrm{id}$).
- **One ambient group.** Extension by the identity is an injective homomorphism from the order
  automorphisms of $[0,1]$ to those of $\mathbb{R}$. It preserves Dlab's order, and its image is
  exactly the maps fixing every point outside $(0,1)$. So each group on $[0,1]$ is isomorphic,
  with its order, to its copy in `IsDlabGroup`. The proof file checks these facts.
- **The linked Lean proof for `variants.not_inner`.** The theorem `kourovka_21_149` of
  pitmonticone/Kourovka works with $D_H([0,1])$ as a group of order automorphisms of $[0,1]$,
  with the same local definitions. It gives an order automorphism, for the first-disagreement
  order, that is not inner. Here that group appears through its extension to $\mathbb{R}$.

AI Usage Disclosure: This formalization and the external proof were developed with assistance
from Anthropic's Claude (Claude Code), under the direction of KitaKen1 (Kenta Kitamura).
