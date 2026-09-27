import FormalConjecturesUtil

/-!
# Kourovka Notebook Problem 21.149

> Are there order automorphisms of Dlab groups that are not induced by conjugation by elements
> of a (possibly bigger) Dlab group?

This file proves the Formal Conjectures-style statement `Kourovka.«21.149».kourovka_21_149`
of `FClikeLean/21_149.lean` with the answer `True`. The definitions of the statement are copied
verbatim from that file.

The statement views every Dlab group inside the order automorphisms of `ℝ`: an order automorphism
of `[0,1]` is extended by the identity. The witness is `G = D_K([0,1])` with Dlab's order and the
order automorphism `αo f = h⁻¹ f h`, where `h` is a two-ended alternating-slope homeomorphism of
`[0,1]`. `αo` is not induced through
any injective homomorphism into any of the six Dlab groups with any slope group `H`
(`Kourovka21149.kourovka_21_149_injective`, for every nontrivial `K`).

The development below consists of the modules of the project in dependency order. The section
`Dlab` is vendored from https://github.com/pitmonticone/Kourovka (Apache-2.0).
-/

/- ## Section: `Statement` (verbatim from `FClikeLean/21_149.lean`) -/

section Statement

open Filter Topology

namespace Kourovka.«21.149»

/--
An order automorphism $f$ of $\mathbb{R}$ is *locally right $H$-linear* if every point has a
right neighbourhood on which $f$ is affine with slope in $H \le \mathbb{R}_{>0}$.
-/
def IsLocallyRightLinear (H : Subgroup NNRealˣ) (f : ℝ ≃o ℝ) : Prop :=
  ∀ a : ℝ, ∃ ε > (0 : ℝ), ∃ h ∈ H, ∀ x : ℝ, a < x → x < a + ε →
    f x = f a + ((h : NNReal) : ℝ) * (x - a)

/--
$A$ is one of the six Dlab groups with slope group $H$. Each consists of the locally right
$H$-linear order automorphisms $f$ with a condition at the ends.

- Four act on $I = [0, 1]$. An order automorphism of $I$ is identified with its extension to
  $\mathbb{R}$ by the identity, so $f$ fixes every point outside $(0, 1)$. The four groups are
  $D_H(I)$ ($f$ is also the identity near $0$ and near $1$), $D_{H*}(I)$ (near $0$),
  $D_{*H}(I)$ (near $1$) and $\overline{D}_H(I)$ (no further condition).
- Two act on the extended real line $\overline{\mathbb{R}}$, whose order automorphisms are those
  of $\mathbb{R}$. They are $D_H$ ($f$ is the identity near $-\infty$ and near $+\infty$) and
  $D_{H*}$ (near $-\infty$).
-/
def IsDlabGroup (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)) : Prop :=
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    (∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∧ ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∧
    ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ x ∉ Set.Ioo (0 : ℝ) 1, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ (∀ᶠ x in atBot, f x = x) ∧
    ∀ᶠ x in atTop, f x = x) ∨
  (∀ f, f ∈ A ↔ IsLocallyRightLinear H f ∧ ∀ᶠ x in atBot, f x = x)

/--
Dlab's order on a group $G$ of order automorphisms of $\mathbb{R}$: $f < g$ if $f(x) < g(x)$ at
some point $x$ and every point $y$ with $g(y) < f(y)$ lies to the right of $x$. For elements of
a Dlab group, this says that $f$ is below $g$ just after the point where they start to differ.
-/
def DlabLt {G : Subgroup (ℝ ≃o ℝ)} (f g : G) : Prop :=
  ∃ x, (f : ℝ ≃o ℝ) x < (g : ℝ ≃o ℝ) x ∧ ∀ y, (g : ℝ ≃o ℝ) y < (f : ℝ ≃o ℝ) y → x < y

end Kourovka.«21.149»

end Statement

/- ## Section: `Dlab` -/

section

/-
Vendored from https://github.com/pitmonticone/Kourovka
(file `Kourovka/Mathlib/GroupTheory/Orderable/Dlab/Basic.lean`, Apache-2.0).
Original copyright notice follows; only the imports and this note were changed.
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin, Pietro Monticone, Daniel Morrison
-/


/-
# Dlab groups on the unit interval

For a subgroup `H` of the positive real numbers, this file defines Dlab's group of locally right
`H`-linear order automorphisms of the unit interval whose support is bounded away from both
endpoints.

The paper also studies variants obtained by dropping one or both endpoint conditions. `DlabGroup`
denotes the variant that is the identity near both endpoints.

## Main definitions

* `Dlab.IsLocallyRightHLinear`: the local right-affinity condition with slopes in `H`.
* `Dlab.IsElement`: the predicate defining the compact-support interval Dlab group.
* `Dlab.subgroup`: the Dlab group as a subgroup of the order automorphisms of `[0, 1]`.
* `DlabGroup`: the corresponding bundled group type.

## Implementation notes

The positive real numbers are represented by the units `NNRealˣ`. Multiplication of interval order
automorphisms uses mathlib's standard relation-isomorphism convention, `(f * g) x = f (g x)`.

## References

* [V. Dlab, *On a Family of Simple Ordered Groups*](https://doi.org/10.1017/S1446788700006261)
-/

open scoped unitInterval Topology

namespace Dlab

/-- The order automorphisms of the closed unit interval. -/
abbrev IntervalAut := unitInterval ≃o unitInterval

/-- Coerce a positive real unit to a real number. -/
abbrev slopeToReal (h : NNRealˣ) : ℝ := ((h : NNReal) : ℝ)

/-- An interval automorphism is *locally right `H`-linear* if its germ to the right of each point
other than `1` is affine with slope in `H`. -/
def IsLocallyRightHLinear (H : Subgroup NNRealˣ) (f : IntervalAut) : Prop :=
  ∀ a : unitInterval, a < 1 → ∃ ε : ℝ, 0 < ε ∧ ∃ h : H, ∀ ⦃x : unitInterval⦄,
    (a : ℝ) < x → (x : ℝ) < (a : ℝ) + ε →
    (f x : ℝ) = (f a : ℝ) + slopeToReal h.1 * ((x : ℝ) - (a : ℝ))

/-- `f` is the identity on some neighborhood of `0`. -/
def IsIdentityNearZero (f : IntervalAut) : Prop :=
  f =ᶠ[𝓝 (0 : unitInterval)] id

/-- `f` is the identity on some neighborhood of `1`. -/
def IsIdentityNearOne (f : IntervalAut) : Prop :=
  f =ᶠ[𝓝 (1 : unitInterval)] id

/-- An interval automorphism is a Dlab element if it is locally right `H`-linear and is the
identity near both endpoints. -/
def IsElement (H : Subgroup NNRealˣ) (f : IntervalAut) : Prop :=
  IsLocallyRightHLinear H f ∧ IsIdentityNearZero f ∧ IsIdentityNearOne f

/-- Local right-linearity is monotone in the allowed slope subgroup. -/
theorem IsLocallyRightHLinear.mono {H K : Subgroup NNRealˣ} {f : IntervalAut}
    (hf : IsLocallyRightHLinear H f) (hHK : H ≤ K) : IsLocallyRightHLinear K f := by
  intro a ha
  obtain ⟨ε, hε, h, hh⟩ := hf a ha
  exact ⟨ε, hε, ⟨h, hHK h.2⟩, hh⟩

/-- The Dlab-element predicate is monotone in the allowed slope subgroup. -/
theorem IsElement.mono {H K : Subgroup NNRealˣ} {f : IntervalAut} (hf : IsElement H f)
    (hHK : H ≤ K) : IsElement K f :=
  ⟨hf.1.mono hHK, hf.2⟩

/-- The identity is a Dlab element for every slope subgroup. -/
theorem isElement_one (H : Subgroup NNRealˣ) : IsElement H (1 : IntervalAut) :=
  ⟨fun a _ ↦ ⟨1, zero_lt_one, 1, fun _ _ ↦ by norm_num [slopeToReal]⟩,
    by simp [IsIdentityNearZero], by simp [IsIdentityNearOne]⟩

/-- Composition preserves local right `H`-linearity. -/
theorem isLocallyRightHLinear_mul {H : Subgroup NNRealˣ} {f g : IntervalAut}
    (hf : IsLocallyRightHLinear H f) (hg : IsLocallyRightHLinear H g) :
    IsLocallyRightHLinear H (f * g) := by
  intro a ha
  obtain ⟨ε₁, hε₁, h₁, hh₁⟩ := hg a ha
  obtain ⟨ε₂, hε₂, h₂, hh₂⟩ := hf (g a) (by
    simpa only [show g 1 = 1 from g.map_top] using g.strictMono ha)
  have h₁_pos : 0 < slopeToReal h₁ := by simp [slopeToReal]
  refine ⟨min ε₁ (ε₂ / slopeToReal h₁), lt_min hε₁ (div_pos hε₂ h₁_pos), h₂ * h₁,
    fun x hx₁ hx₂ ↦ ?_⟩
  have hg_eq := hh₁ hx₁ (by linarith [min_le_left ε₁ (ε₂ / slopeToReal h₁)])
  have hf_eq :=
    hh₂ (g.strictMono hx₁) (by
      nlinarith [min_le_right ε₁ (ε₂ / slopeToReal h₁),
        mul_div_cancel₀ ε₂ (ne_of_gt h₁_pos)])
  simp only [RelIso.mul_apply, slopeToReal, Subgroup.coe_mul, Units.val_mul, NNReal.coe_mul,
    hg_eq, hf_eq]
  ring

/-- The product of two Dlab elements is a Dlab element. -/
theorem isElement_mul {H : Subgroup NNRealˣ} {f g : IntervalAut}
    (hf : IsElement H f) (hg : IsElement H g) : IsElement H (f * g) := by
  refine ⟨isLocallyRightHLinear_mul hf.1 hg.1, ?_, ?_⟩
  · filter_upwards [hf.2.1, hg.2.1] with x hfx hgx
    simp only [RelIso.mul_apply, id_eq, hgx, hfx]
  · filter_upwards [hf.2.2, hg.2.2] with x hfx hgx
    simp only [RelIso.mul_apply, id_eq, hgx, hfx]

/-- Inversion preserves local right `H`-linearity. -/
theorem isLocallyRightHLinear_inv {H : Subgroup NNRealˣ} {f : IntervalAut}
    (hf : IsLocallyRightHLinear H f) : IsLocallyRightHLinear H f⁻¹ := by
  intro a ha
  obtain ⟨ε, hε_pos, h, hh⟩ := hf (f⁻¹ a) (by
    simpa only [show f⁻¹ 1 = 1 from f⁻¹.map_top] using f⁻¹.strictMono ha)
  obtain ⟨hε', hε'_pos, hε'_eq⟩ : ∃ ε' > 0, ∀ x : unitInterval, (a : ℝ) < x →
      (x : ℝ) < (a : ℝ) + ε' → (f⁻¹ x : ℝ) < (f⁻¹ a : ℝ) + ε := by
    have hcont : Continuous fun x : unitInterval ↦ (f⁻¹ x : ℝ) := by continuity
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuous_iff.mp hcont a ε hε_pos
    refine ⟨δ, hδ_pos, fun x hx₁ hx₂ ↦ ?_⟩
    have hout := hδ x (by
      rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx₁.le)]
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hx₂))
    rw [Real.dist_eq] at hout
    simpa [add_comm] using (sub_lt_iff_lt_add.mp (abs_lt.mp hout).2)
  refine ⟨hε', hε'_pos, h⁻¹, fun x hx₁ hx₂ ↦ ?_⟩
  have hfx := hh (f⁻¹.strictMono hx₁) (hε'_eq x hx₁ hx₂)
  simp_all [slopeToReal]

/-- Being the identity near `0` is preserved by inversion. -/
theorem isIdentityNearZero_inv {f : IntervalAut} (hf : IsIdentityNearZero f) :
    IsIdentityNearZero f⁻¹ := by
  filter_upwards [hf] with x hx
  change f.symm x = x
  simpa only [OrderIso.symm_apply_eq, id_eq] using hx.symm

/-- Being the identity near `1` is preserved by inversion. -/
theorem isIdentityNearOne_inv {f : IntervalAut} (hf : IsIdentityNearOne f) :
    IsIdentityNearOne f⁻¹ := by
  filter_upwards [hf] with x hx
  change f.symm x = x
  simpa only [OrderIso.symm_apply_eq, id_eq] using hx.symm

/-- The inverse of a Dlab element is a Dlab element. -/
theorem isElement_inv {H : Subgroup NNRealˣ} {f : IntervalAut} (hf : IsElement H f) :
    IsElement H f⁻¹ :=
  ⟨isLocallyRightHLinear_inv hf.1, isIdentityNearZero_inv hf.2.1, isIdentityNearOne_inv hf.2.2⟩

/-- Dlab's compact-support interval group with slopes in `H`, as a subgroup of the order
automorphisms of `[0, 1]`. -/
def subgroup (H : Subgroup NNRealˣ) : Subgroup IntervalAut where
  carrier := {f | IsElement H f}
  one_mem' := isElement_one H
  mul_mem' := isElement_mul
  inv_mem' := isElement_inv

/-- Membership in `subgroup H` is the Dlab-element predicate for `H`. -/
@[simp]
theorem mem_subgroup {H : Subgroup NNRealˣ} {f : IntervalAut} :
    f ∈ subgroup H ↔ IsElement H f := Iff.rfl

/-- The Dlab subgroup is monotone in the allowed slope subgroup. -/
theorem subgroup_mono : Monotone subgroup :=
  fun _ _ hHK _ hf ↦ hf.mono hHK

end Dlab

/-- Dlab's compact-support interval group with slopes in `H`, as a bundled group type. -/
abbrev DlabGroup (H : Subgroup NNRealˣ) := ↥(Dlab.subgroup H)

end

/- ## Section: `Basic` -/

section

/-
# Order automorphisms of the real line

We work with `LineAut := ℝ ≃o ℝ`, the increasing homeomorphisms of `ℝ`. All Dlab groups studied
in this project act on `ℝ` (the interval groups after extension by the identity).

## Main definitions

* `FDLt a b`: the strict *first-disagreement* relation (Dlab's order).
* `fixLeft s`: the subgroup of elements that fix every point `≤ s`.
* `fm a`: the first moved point of `a`, i.e. `sInf {x | a x ≠ x}`.
* `IsDlabLike a`: `a` is the identity near `-∞` and affine on a right neighbourhood of each
  of its fixed points. Every element of every Dlab group considered here has this property.

## Main results

* `IsDlabLike.one_fdlt_or_fdlt_one`: the first-disagreement relation is total.
* `mem_fixLeft_of_fdlt`: the subgroups `fixLeft s` are convex for the first-disagreement order.
* `fdlt_of_fm_lt`: an element with a later first moved point is smaller in absolute value.
* `commutator_eq_self_near`: a commutator of elements that are affine to the right of a common
  fixed point is the identity to the right of that point.
* `no_staircase`: an element of a Dlab-like group cannot have infinitely many support
  components accumulating downwards.
-/

open Set

namespace Kourovka21149

/-- Increasing homeomorphisms of the real line, i.e. order automorphisms of `ℝ`. -/
abbrev LineAut := ℝ ≃o ℝ

namespace LineAut

lemma mul_apply' (a b : LineAut) (x : ℝ) : (a * b) x = a (b x) := rfl

lemma one_apply' (x : ℝ) : (1 : LineAut) x = x := rfl

lemma inv_apply_apply (a : LineAut) (x : ℝ) : a⁻¹ (a x) = x := a.symm_apply_apply x

lemma apply_inv_apply (a : LineAut) (x : ℝ) : a (a⁻¹ x) = x := a.apply_symm_apply x

lemma inv_apply_eq_of_apply_eq {a : LineAut} {x : ℝ} (h : a x = x) : a⁻¹ x = x := by
  calc a⁻¹ x = a⁻¹ (a x) := by rw [h]
    _ = x := inv_apply_apply a x

lemma apply_eq_of_inv_apply_eq {a : LineAut} {x : ℝ} (h : a⁻¹ x = x) : a x = x := by
  calc a x = a (a⁻¹ x) := by rw [h]
    _ = x := apply_inv_apply a x

lemma inv_apply_eq_iff {a : LineAut} {x : ℝ} : a⁻¹ x = x ↔ a x = x :=
  ⟨apply_eq_of_inv_apply_eq, inv_apply_eq_of_apply_eq⟩

lemma ext_iff' {a b : LineAut} : a = b ↔ ∀ x, a x = b x :=
  ⟨fun h _ ↦ h ▸ rfl, fun h ↦ RelIso.ext h⟩

lemma eq_one_iff {a : LineAut} : a = 1 ↔ ∀ x, a x = x := ext_iff'

/-- An element fixing every point below `p` fixes `p`. -/
lemma apply_eq_of_forall_lt (a : LineAut) {p : ℝ} (h : ∀ x < p, a x = x) : a p = p := by
  have key : ∀ b : LineAut, (∀ x < p, b x = x) → p ≤ b p := by
    intro b hb
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨d, hcd, hdp⟩ := exists_between hc
    calc c < d := hcd
      _ = b d := (hb d hdp).symm
      _ ≤ b p := b.monotone hdp.le
  have h1 := key a h
  have h2 := key a⁻¹ fun x hx ↦ inv_apply_eq_of_apply_eq (h x hx)
  have h3 : a p ≤ a (a⁻¹ p) := a.monotone h2
  rw [apply_inv_apply] at h3
  exact le_antisymm h3 h1

end LineAut

open LineAut

/- ## The first-disagreement relation -/

/-- The strict first-disagreement relation: `a` is below `b` iff there is a point where `a` is
below `b` such that every point where `b` is below `a` lies to its right. This is Dlab's order. -/
def FDLt (a b : LineAut) : Prop :=
  ∃ x, a x < b x ∧ ∀ y, b y < a y → x < y

lemma fdlt_irrefl (a : LineAut) : ¬ FDLt a a := fun ⟨_, h, _⟩ ↦ lt_irrefl _ h

lemma fdlt_asymm {a b : LineAut} (h : FDLt a b) : ¬ FDLt b a := by
  rintro ⟨y, hy, hy'⟩
  obtain ⟨x, hx, hx'⟩ := h
  have h1 := hx' y hy
  have h2 := hy' x hx
  linarith

lemma fdlt_trans {a b c : LineAut} (hab : FDLt a b) (hbc : FDLt b c) : FDLt a c := by
  obtain ⟨x, hx, hx'⟩ := hab
  obtain ⟨x', hy, hy'⟩ := hbc
  rcases le_or_gt x x' with hxx | hxx
  · refine ⟨x, ?_, fun y hy'' ↦ ?_⟩
    · have : b x ≤ c x := by
        by_contra hcon
        push Not at hcon
        have := hy' x hcon
        linarith
      linarith
    · by_contra hyx
      push Not at hyx
      rcases lt_or_ge (c y) (b y) with hcb | hcb
      · have := hy' y hcb
        linarith
      · have := hx' y (by linarith)
        linarith
  · refine ⟨x', ?_, fun y hy'' ↦ ?_⟩
    · have : a x' ≤ b x' := by
        by_contra hcon
        push Not at hcon
        have := hx' x' hcon
        linarith
      linarith
    · by_contra hyx
      push Not at hyx
      rcases lt_or_ge (c y) (b y) with hcb | hcb
      · have := hy' y hcb
        linarith
      · have := hx' y (by linarith)
        linarith

lemma fdlt_mul_left (c : LineAut) {a b : LineAut} (h : FDLt a b) : FDLt (c * a) (c * b) := by
  obtain ⟨x, hx, hx'⟩ := h
  refine ⟨x, c.strictMono hx, fun y hy ↦ hx' y (c.strictMono.lt_iff_lt.mp hy)⟩

lemma fdlt_mul_right (c : LineAut) {a b : LineAut} (h : FDLt a b) : FDLt (a * c) (b * c) := by
  obtain ⟨x, hx, hx'⟩ := h
  refine ⟨c⁻¹ x, ?_, fun y hy ↦ ?_⟩
  · simpa [mul_apply', apply_inv_apply] using hx
  · have := hx' (c y) hy
    have h2 := c⁻¹.strictMono this
    rwa [inv_apply_apply] at h2

lemma fdlt_mul_left_iff (c : LineAut) {a b : LineAut} : FDLt (c * a) (c * b) ↔ FDLt a b :=
  ⟨fun h ↦ by simpa [mul_assoc] using fdlt_mul_left c⁻¹ h, fdlt_mul_left c⟩

lemma fdlt_mul_right_iff (c : LineAut) {a b : LineAut} : FDLt (a * c) (b * c) ↔ FDLt a b :=
  ⟨fun h ↦ by simpa [mul_assoc] using fdlt_mul_right c⁻¹ h, fdlt_mul_right c⟩

/-- Conjugation by any increasing homeomorphism preserves the first-disagreement relation. -/
lemma fdlt_conj_iff (c : LineAut) {a b : LineAut} :
    FDLt (c⁻¹ * a * c) (c⁻¹ * b * c) ↔ FDLt a b := by
  rw [fdlt_mul_right_iff, fdlt_mul_left_iff]

lemma fdlt_inv {a b : LineAut} (h : FDLt a b) : FDLt b⁻¹ a⁻¹ := by
  have h1 := fdlt_mul_left a⁻¹ h
  rw [inv_mul_cancel] at h1
  have h2 := fdlt_mul_right b⁻¹ h1
  simpa [mul_assoc] using h2

lemma one_fdlt_inv_iff {a : LineAut} : FDLt 1 a⁻¹ ↔ FDLt a 1 := by
  constructor
  · intro h
    have := fdlt_inv h
    simpa using this
  · intro h
    have := fdlt_inv h
    simpa using this

/- ## Subgroups fixing a left ray -/

/-- The subgroup of elements fixing every point `≤ s`. -/
def fixLeft (s : ℝ) : Subgroup LineAut where
  carrier := {a | ∀ x ≤ s, a x = x}
  mul_mem' := by
    intro a b ha hb x hx
    change a (b x) = x
    rw [hb x hx, ha x hx]
  one_mem' := fun _ _ ↦ rfl
  inv_mem' := by
    intro a ha x hx
    exact inv_apply_eq_of_apply_eq (ha x hx)

@[simp] lemma mem_fixLeft {s : ℝ} {a : LineAut} : a ∈ fixLeft s ↔ ∀ x ≤ s, a x = x := Iff.rfl

lemma fixLeft_anti {s s' : ℝ} (h : s' ≤ s) : fixLeft s ≤ fixLeft s' :=
  fun _ ha x hx ↦ ha x (hx.trans h)

/- ## The first moved point -/

/-- The set of points moved by `a`. -/
def movedSet (a : LineAut) : Set ℝ := {x | a x ≠ x}

/-- The first moved point of `a`. -/
noncomputable def fm (a : LineAut) : ℝ := sInf (movedSet a)

/-- `a` is the identity on a left ray. -/
def IdNearBot (a : LineAut) : Prop := ∃ c, ∀ x ≤ c, a x = x

/-- `a` is affine on a right neighbourhood of `p`. -/
def RightAffineAt (a : LineAut) (p : ℝ) : Prop :=
  ∃ ε > 0, ∃ k : ℝ, ∀ x, p ≤ x → x < p + ε → a x = a p + k * (x - p)

/-- The two properties of elements of Dlab groups used in the proofs: being the identity near
`-∞`, and being affine to the right of every fixed point. -/
structure IsDlabLike (a : LineAut) : Prop where
  idNearBot : IdNearBot a
  rightAffine : ∀ p, a p = p → RightAffineAt a p

lemma movedSet_inv (a : LineAut) : movedSet a⁻¹ = movedSet a := by
  ext x
  simp only [movedSet, Set.mem_ofPred_eq, ne_eq]
  rw [inv_apply_eq_iff]

lemma fm_inv (a : LineAut) : fm a⁻¹ = fm a := by
  simp [fm, movedSet_inv]

lemma movedSet_nonempty {a : LineAut} (h : a ≠ 1) : (movedSet a).Nonempty := by
  by_contra hne
  apply h
  rw [eq_one_iff]
  intro x
  by_contra hx
  exact hne ⟨x, hx⟩

lemma movedSet_bddBelow {a : LineAut} (h : IdNearBot a) : BddBelow (movedSet a) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun x hx ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  exact hx (hc x hlt.le)

lemma apply_of_lt_fm {a : LineAut} (h : IdNearBot a) {x : ℝ} (hx : x < fm a) : a x = x := by
  by_contra hne
  have := csInf_le (movedSet_bddBelow h) hne
  exact absurd this (not_le.mpr hx)

lemma apply_fm {a : LineAut} (h : IdNearBot a) : a (fm a) = fm a :=
  apply_eq_of_forall_lt a fun _ hx ↦ apply_of_lt_fm h hx

lemma apply_of_le_fm {a : LineAut} (h : IdNearBot a) {x : ℝ} (hx : x ≤ fm a) : a x = x := by
  rcases hx.lt_or_eq with hx | hx
  · exact apply_of_lt_fm h hx
  · rw [hx]; exact apply_fm h

lemma fm_le_of_moved {a : LineAut} (h : IdNearBot a) {x : ℝ} (hx : a x ≠ x) : fm a ≤ x :=
  csInf_le (movedSet_bddBelow h) hx

lemma fm_lt_of_moved {a : LineAut} (h : IdNearBot a) {x : ℝ} (hx : a x ≠ x) : fm a < x := by
  rcases (fm_le_of_moved h hx).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (h' ▸ apply_fm h) hx

lemma exists_moved_lt {a : LineAut} (h1 : a ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, a x ≠ x ∧ x < fm a + ε := by
  obtain ⟨x, hx, hlt⟩ := exists_lt_of_csInf_lt (movedSet_nonempty h1) (lt_add_of_pos_right _ hε)
  exact ⟨x, hx, hlt⟩

lemma le_fm_of_forall {a : LineAut} (h1 : a ≠ 1) {p : ℝ} (h : ∀ x < p, a x = x) : p ≤ fm a := by
  refine le_csInf (movedSet_nonempty h1) fun x hx ↦ ?_
  by_contra hlt
  push Not at hlt
  exact hx (h x hlt)

lemma fm_le_of_forall {a : LineAut} (h1 : a ≠ 1) (hb : IdNearBot a) {q : ℝ}
    (h : ∀ x, q < x → a x = x) : fm a ≤ q := by
  obtain ⟨x, hx⟩ := movedSet_nonempty h1
  have hxq : x ≤ q := by
    by_contra hlt
    push Not at hlt
    exact hx (h x hlt)
  exact (fm_le_of_moved hb hx).trans hxq

/-- If every point of `(p, p + δ)` exceeds `x`, then `x ≤ p`. -/
lemma le_of_forall_Ioo_lt {x p δ : ℝ} (hδ : 0 < δ) (h : ∀ y, p < y → y < p + δ → x < y) :
    x ≤ p := by
  by_contra hlt
  push Not at hlt
  have hmin : 0 < min (x - p) δ := lt_min (by linarith) hδ
  have h1 := h (p + min (x - p) δ / 2) (by linarith) (by linarith [min_le_right (x - p) δ])
  linarith [min_le_left (x - p) δ]

/- ## Conjugation -/

lemma movedSet_conj (c b : LineAut) :
    movedSet (c⁻¹ * b * c) = ⇑(c⁻¹ : LineAut) '' movedSet b := by
  ext x
  constructor
  · intro hx
    refine ⟨c x, fun hbx ↦ hx ?_, inv_apply_apply c x⟩
    show c⁻¹ (b (c x)) = x
    rw [hbx, inv_apply_apply]
  · rintro ⟨y, hy, rfl⟩ h
    apply hy
    have h' : c⁻¹ (b (c (c⁻¹ y))) = c⁻¹ y := h
    rw [apply_inv_apply] at h'
    exact c⁻¹.injective h'

lemma fm_conj (c b : LineAut) (hb : IdNearBot b) (h1 : b ≠ 1) :
    fm (c⁻¹ * b * c) = c⁻¹ (fm b) := by
  unfold fm
  rw [movedSet_conj]
  exact (OrderIso.map_csInf' c⁻¹ (movedSet_nonempty h1) (movedSet_bddBelow hb)).symm

lemma mem_fixLeft_conj_iff (U b : LineAut) (s : ℝ) :
    U⁻¹ * b * U ∈ fixLeft (U⁻¹ s) ↔ b ∈ fixLeft s := by
  constructor
  · intro h x hx
    have hy : U⁻¹ x ≤ U⁻¹ s := U⁻¹.monotone hx
    have h' := h (U⁻¹ x) hy
    change U⁻¹ (b (U (U⁻¹ x))) = U⁻¹ x at h'
    rw [apply_inv_apply] at h'
    exact U⁻¹.injective h'
  · intro h y hy
    have hUy : U y ≤ s := by
      have := U.monotone hy
      rwa [apply_inv_apply] at this
    show U⁻¹ (b (U y)) = y
    rw [h (U y) hUy, inv_apply_apply]

/- ## Slopes at the first moved point -/

lemma RightAffineAt.slope_pos {a : LineAut} {p ε k : ℝ} (hε : 0 < ε)
    (h : ∀ x, p ≤ x → x < p + ε → a x = a p + k * (x - p)) : 0 < k := by
  have hx := h (p + ε / 2) (by linarith) (by linarith)
  have hlt : a p < a (p + ε / 2) := a.strictMono (by linarith)
  rw [hx] at hlt
  have : 0 < k * (ε / 2) := by linarith
  exact pos_of_mul_pos_left this (by linarith)

namespace IsDlabLike

variable {a : LineAut}

lemma exists_slope (ha : IsDlabLike a) (h1 : a ≠ 1) :
    ∃ ε > 0, ∃ k, 0 < k ∧ k ≠ 1 ∧
      ∀ x, fm a ≤ x → x < fm a + ε → a x = fm a + k * (x - fm a) := by
  obtain ⟨ε, hε, k, hk⟩ := ha.rightAffine (fm a) (apply_fm ha.idNearBot)
  have hk' : ∀ x, fm a ≤ x → x < fm a + ε → a x = fm a + k * (x - fm a) := by
    intro x hx1 hx2
    rw [hk x hx1 hx2, apply_fm ha.idNearBot]
  refine ⟨ε, hε, k, RightAffineAt.slope_pos hε hk, ?_, hk'⟩
  rintro rfl
  obtain ⟨x, hx, hxlt⟩ := exists_moved_lt h1 hε
  have hfx := fm_lt_of_moved ha.idNearBot hx
  apply hx
  rw [hk' x hfx.le hxlt]
  ring

/-- A nontrivial Dlab-like element moves every point of some right neighbourhood of its first
moved point, all in the same direction. -/
lemma moves_right_or_left (ha : IsDlabLike a) (h1 : a ≠ 1) :
    ∃ ε > 0, (∀ x, fm a < x → x < fm a + ε → x < a x) ∨
      (∀ x, fm a < x → x < fm a + ε → a x < x) := by
  obtain ⟨ε, hε, k, hk0, hk1, hk⟩ := ha.exists_slope h1
  refine ⟨ε, hε, ?_⟩
  rcases lt_or_gt_of_ne hk1 with hlt | hgt
  · right
    intro x hx1 hx2
    rw [hk x hx1.le hx2]
    nlinarith
  · left
    intro x hx1 hx2
    rw [hk x hx1.le hx2]
    nlinarith

lemma one_fdlt_of_moves_right (ha : IsDlabLike a) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, fm a < x → x < fm a + ε → x < a x) : FDLt 1 a := by
  refine ⟨fm a + ε / 2, ?_, fun y hy ↦ ?_⟩
  · show fm a + ε / 2 < a (fm a + ε / 2)
    exact h (fm a + ε / 2) (by linarith) (by linarith)
  by_contra hyx
  push Not at hyx
  rcases le_or_gt y (fm a) with hy' | hy'
  · rw [apply_of_le_fm ha.idNearBot hy'] at hy
    exact lt_irrefl _ hy
  · have := h y hy' (by linarith)
    exact lt_asymm hy this

lemma fdlt_one_of_moves_left (ha : IsDlabLike a) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x, fm a < x → x < fm a + ε → a x < x) : FDLt a 1 := by
  refine ⟨fm a + ε / 2, ?_, fun y hy ↦ ?_⟩
  · show a (fm a + ε / 2) < fm a + ε / 2
    exact h (fm a + ε / 2) (by linarith) (by linarith)
  by_contra hyx
  push Not at hyx
  rcases le_or_gt y (fm a) with hy' | hy'
  · change y < a y at hy
    rw [apply_of_le_fm ha.idNearBot hy'] at hy
    exact lt_irrefl _ hy
  · have := h y hy' (by linarith)
    exact lt_asymm hy this

lemma one_fdlt_or_fdlt_one (ha : IsDlabLike a) (h1 : a ≠ 1) : FDLt 1 a ∨ FDLt a 1 := by
  obtain ⟨ε, hε, h | h⟩ := ha.moves_right_or_left h1
  · exact Or.inl (ha.one_fdlt_of_moves_right hε h)
  · exact Or.inr (ha.fdlt_one_of_moves_left hε h)

/-- A positive element moves points to the right just after its first moved point. -/
lemma moves_right_of_one_fdlt (ha : IsDlabLike a) (h1 : a ≠ 1) (hpos : FDLt 1 a) :
    ∃ ε > 0, ∀ x, fm a < x → x < fm a + ε → x < a x := by
  obtain ⟨ε, hε, h | h⟩ := ha.moves_right_or_left h1
  · exact ⟨ε, hε, h⟩
  · exact absurd hpos (fdlt_asymm (ha.fdlt_one_of_moves_left hε h))

/-- A negative element moves points to the left just after its first moved point. -/
lemma moves_left_of_fdlt_one (ha : IsDlabLike a) (h1 : a ≠ 1) (hneg : FDLt a 1) :
    ∃ ε > 0, ∀ x, fm a < x → x < fm a + ε → a x < x := by
  obtain ⟨ε, hε, h | h⟩ := ha.moves_right_or_left h1
  · exact absurd hneg (fdlt_asymm (ha.one_fdlt_of_moves_right hε h))
  · exact ⟨ε, hε, h⟩

end IsDlabLike

/-- Trichotomy of the first-disagreement relation, for elements whose quotient is Dlab-like. -/
lemma fdlt_trichotomy {a b : LineAut} (h : IsDlabLike (a⁻¹ * b)) :
    a = b ∨ FDLt a b ∨ FDLt b a := by
  by_cases hab : a = b
  · exact Or.inl hab
  have h1 : a⁻¹ * b ≠ 1 := by
    intro h'
    apply hab
    have := congrArg (a * ·) h'
    simpa [mul_assoc] using this.symm
  rcases h.one_fdlt_or_fdlt_one h1 with h2 | h2
  · right; left
    have := fdlt_mul_left a h2
    simpa [mul_assoc] using this
  · right; right
    have := fdlt_mul_left a h2
    simpa [mul_assoc] using this

/- ## Convexity of `fixLeft s` -/

/-- If `1 < b < a` and `a` fixes `(-∞, s]`, then so does `b`. -/
lemma mem_fixLeft_of_fdlt {a b : LineAut} {s : ℝ} (hb : IsDlabLike b) (h1 : FDLt 1 b)
    (h2 : FDLt b a) (ha : a ∈ fixLeft s) : b ∈ fixLeft s := by
  intro z hz
  by_contra hbz
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbz rfl
  have hfz := fm_lt_of_moved hb.idNearBot hbz
  obtain ⟨ε, hε, hright⟩ := hb.moves_right_of_one_fdlt hb1 h1
  obtain ⟨x1, hx1, hx1'⟩ := h2
  have hδ : 0 < min ε (s - fm b) := lt_min hε (by linarith)
  have hx1le : x1 ≤ fm b := by
    refine le_of_forall_Ioo_lt hδ fun y hy1 hy2 ↦ hx1' y ?_
    have hys : y ≤ s := by linarith [min_le_right ε (s - fm b)]
    rw [ha y hys]
    exact hright y hy1 (by linarith [min_le_left ε (s - fm b)])
  rw [apply_of_le_fm hb.idNearBot hx1le, ha x1 (by linarith)] at hx1
  exact lt_irrefl _ hx1

/-- If `a < b < 1` and `a` fixes `(-∞, s]`, then so does `b`. -/
lemma mem_fixLeft_of_fdlt' {a b : LineAut} {s : ℝ} (hb : IsDlabLike b) (h1 : FDLt b 1)
    (h2 : FDLt a b) (ha : a ∈ fixLeft s) : b ∈ fixLeft s := by
  intro z hz
  by_contra hbz
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbz rfl
  have hfz := fm_lt_of_moved hb.idNearBot hbz
  obtain ⟨ε, hε, hleft⟩ := hb.moves_left_of_fdlt_one hb1 h1
  obtain ⟨x1, hx1, hx1'⟩ := h2
  have hδ : 0 < min ε (s - fm b) := lt_min hε (by linarith)
  have hx1le : x1 ≤ fm b := by
    refine le_of_forall_Ioo_lt hδ fun y hy1 hy2 ↦ hx1' y ?_
    have hys : y ≤ s := by linarith [min_le_right ε (s - fm b)]
    rw [ha y hys]
    exact hleft y hy1 (by linarith [min_le_left ε (s - fm b)])
  rw [apply_of_le_fm hb.idNearBot hx1le, ha x1 (by linarith)] at hx1
  exact lt_irrefl _ hx1

/- ## Comparison of elements with different first moved points -/

/-- If `1 < b₀` and `b₀` starts moving before `b`, then `b < b₀`. -/
lemma fdlt_of_fm_lt {b0 b : LineAut} (hb0 : IsDlabLike b0) (hb : IdNearBot b) (h0 : b0 ≠ 1)
    (hlt : fm b0 < fm b) (hpos : FDLt 1 b0) : FDLt b b0 := by
  obtain ⟨ε, hε, hright⟩ := hb0.moves_right_of_one_fdlt h0 hpos
  have hδ : 0 < min ε (fm b - fm b0) := lt_min hε (by linarith)
  set x := fm b0 + min ε (fm b - fm b0) / 2 with hxdef
  have hx1 : fm b0 < x := by linarith
  have hx2 : x < fm b0 + ε := by linarith [min_le_left ε (fm b - fm b0)]
  have hx3 : x < fm b := by linarith [min_le_right ε (fm b - fm b0)]
  refine ⟨x, ?_, fun y hy ↦ ?_⟩
  · rw [apply_of_lt_fm hb hx3]
    exact hright x hx1 hx2
  · by_contra hyx
    push Not at hyx
    rw [apply_of_lt_fm hb (lt_of_le_of_lt hyx hx3)] at hy
    rcases le_or_gt y (fm b0) with hy' | hy'
    · rw [apply_of_le_fm hb0.idNearBot hy'] at hy
      exact lt_irrefl _ hy
    · exact lt_asymm hy (hright y hy' (by linarith))

/- ## Commutators of affine germs -/

lemma inv_apply_of_affine {a : LineAut} {p ε k : ℝ} (hk : 0 < k) (_hfix : a p = p)
    (h : ∀ x, p ≤ x → x < p + ε → a x = p + k * (x - p)) :
    ∀ y, p ≤ y → y < p + k * ε → a⁻¹ y = p + (y - p) / k := by
  intro y hy1 hy2
  have hx1 : p ≤ p + (y - p) / k := by
    have : 0 ≤ (y - p) / k := div_nonneg (by linarith) hk.le
    linarith
  have hx2 : p + (y - p) / k < p + ε := by
    have : (y - p) / k < ε := by rw [div_lt_iff₀ hk]; linarith
    linarith
  have := h _ hx1 hx2
  have hy : a (p + (y - p) / k) = y := by
    rw [this]; field_simp; ring
  calc a⁻¹ y = a⁻¹ (a (p + (y - p) / k)) := by rw [hy]
    _ = p + (y - p) / k := inv_apply_apply a _

/-- A commutator of two elements which fix `p` and are affine to the right of `p` is the
identity on a right neighbourhood of `p`. -/
lemma commutator_eq_self_near {a b : LineAut} {p : ℝ} (hap : a p = p) (hbp : b p = p)
    (ha : RightAffineAt a p) (hb : RightAffineAt b p) :
    ∃ ε > 0, ∀ x, p ≤ x → x < p + ε → (a * b * a⁻¹ * b⁻¹) x = x := by
  obtain ⟨ε1, hε1, k1, h1⟩ := ha
  obtain ⟨ε2, hε2, k2, h2⟩ := hb
  have hk1 := RightAffineAt.slope_pos hε1 h1
  have hk2 := RightAffineAt.slope_pos hε2 h2
  have h1' : ∀ x, p ≤ x → x < p + ε1 → a x = p + k1 * (x - p) := by
    intro x hx1 hx2; rw [h1 x hx1 hx2, hap]
  have h2' : ∀ x, p ≤ x → x < p + ε2 → b x = p + k2 * (x - p) := by
    intro x hx1 hx2; rw [h2 x hx1 hx2, hbp]
  have hi1 := inv_apply_of_affine hk1 hap h1'
  have hi2 := inv_apply_of_affine hk2 hbp h2'
  set δ := min (min (k2 * ε2) (k1 * k2 * ε1)) (min (k1 * k2 * ε2) (k1 * ε1)) with hδ
  have hδpos : 0 < δ := by
    refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> positivity
  refine ⟨δ, hδpos, fun x hx1 hx2 ↦ ?_⟩
  have e1 : x - p < k2 * ε2 := by
    have : δ ≤ k2 * ε2 := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have e2 : x - p < k1 * k2 * ε1 := by
    have : δ ≤ k1 * k2 * ε1 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have e3 : x - p < k1 * k2 * ε2 := by
    have : δ ≤ k1 * k2 * ε2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have e4 : x - p < k1 * ε1 := by
    have : δ ≤ k1 * ε1 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hxp : 0 ≤ x - p := by linarith
  -- step 1: b⁻¹ x
  have s1 : b⁻¹ x = p + (x - p) / k2 := hi2 x hx1 (by linarith)
  -- step 2: a⁻¹ (b⁻¹ x)
  have s2 : a⁻¹ (b⁻¹ x) = p + (x - p) / (k1 * k2) := by
    rw [s1]
    have hq : 0 ≤ (x - p) / k2 := div_nonneg hxp hk2.le
    have hlt : (x - p) / k2 < k1 * ε1 := by
      rw [div_lt_iff₀ hk2]; nlinarith
    rw [hi1 _ (by linarith) (by linarith)]
    field_simp
    ring
  -- step 3: b (a⁻¹ (b⁻¹ x))
  have s3 : b (a⁻¹ (b⁻¹ x)) = p + (x - p) / k1 := by
    rw [s2]
    have hq : 0 ≤ (x - p) / (k1 * k2) := div_nonneg hxp (by positivity)
    have hlt : (x - p) / (k1 * k2) < ε2 := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    rw [h2' _ (by linarith) (by linarith)]
    field_simp
    ring
  -- step 4
  have s4 : a (b (a⁻¹ (b⁻¹ x))) = x := by
    rw [s3]
    have hq : 0 ≤ (x - p) / k1 := div_nonneg hxp hk1.le
    have hlt : (x - p) / k1 < ε1 := by
      rw [div_lt_iff₀ hk1]; linarith
    rw [h1' _ (by linarith) (by linarith)]
    field_simp
    ring
  simpa [mul_apply'] using s4

/- ## No infinite descending staircase -/

/-- A Dlab-like element cannot have a strictly decreasing sequence of fixed points `z m` with a
moved point `s m` between consecutive ones: its support components are well ordered. -/
theorem no_staircase {u : LineAut} (hu : IsDlabLike u) (z s : ℕ → ℝ)
    (hz : ∀ m, u (z m) = z m) (hs : ∀ m, u (s m) ≠ s m) (h1 : ∀ m, z (m + 1) < s m)
    (h2 : ∀ m, s m < z m) : False := by
  have hdec : ∀ m, z (m + 1) < z m := fun m ↦ (h1 m).trans (h2 m)
  by_cases hbdd : BddBelow (range z)
  · set ζ := ⨅ m, z m with hζ
    have hζle : ∀ m, ζ ≤ z m := fun m ↦ ciInf_le hbdd m
    have hζlt : ∀ m, ζ < z m := fun m ↦ lt_of_le_of_lt (hζle (m + 1)) (hdec m)
    have hfix : u ζ = ζ := by
      rw [hζ, OrderIso.map_ciInf u hbdd]
      simp_rw [hz]
    obtain ⟨ε, hε, k, hk⟩ := hu.rightAffine ζ hfix
    obtain ⟨m, hm⟩ := exists_lt_of_ciInf_lt (show ζ < ζ + ε by linarith)
    have hzm := hk (z m) (hζle m) hm
    rw [hz m, hfix] at hzm
    have hk1 : k = 1 := by
      have hpos : 0 < z m - ζ := by linarith [hζlt m]
      have : (k - 1) * (z m - ζ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have hsm := hk (s m) (by linarith [hζle (m + 1), h1 m]) (by linarith [h2 m])
    rw [hfix, hk1] at hsm
    apply hs m
    rw [hsm]
    ring
  · obtain ⟨c, hc⟩ := hu.idNearBot
    have : ∃ m, z m < c := by
      by_contra hcon
      push Not at hcon
      exact hbdd ⟨c, by rintro _ ⟨m, rfl⟩; exact hcon m⟩
    obtain ⟨m, hm⟩ := this
    exact hs m (hc (s m) (by linarith [h2 m]))

end Kourovka21149

end

/- ## Section: `Core` -/

section

/-
# The core argument

This file contains the heart of the proof, stated abstractly.

A *source datum* consists of a group `Γ` acting faithfully on `ℝ` by Dlab-like homeomorphisms
(`ι`), an automorphism `α` of `Γ` realised by conjugation with an increasing homeomorphism `c`
of `ℝ`, and a sequence of fixed points `X m ↓` of `c` such that `c` moves every point between
consecutive fixed points to the right. We also require a supply of elements of `Γ` with small
support (bumps).

`SourceData.false_of_induced` shows: if `e : Γ → LineAut` is an injective homomorphism into
Dlab-like homeomorphisms satisfying the *key property* (which follows from order preservation,
see `Kourovka21149.Order`), then no Dlab-like homeomorphism `U` can induce `α` through `e` by
conjugation.

The proof does not reconstruct the action of `e(Γ)`. For a level `τ`, let `S τ` be the set of
`s` such that some nontrivial `g` with first moved point `< τ` has `e g` fixing `(-∞, s]`, and
let `w τ = sup S τ`. Then `w` is monotone, satisfies `w (c⁻¹ τ) = U⁻¹ (w τ)`, and has no
plateaus (by a commutator argument at the germ level). Hence `U` fixes the points `w (X m)` and
moves a point between any two consecutive ones, which contradicts `no_staircase`.
-/

open Set

namespace Kourovka21149

open LineAut

/-- The data describing the source group and the automorphism `α`. -/
structure SourceData (Γ : Type*) [Group Γ] where
  /-- The standard action of `Γ` on the real line. -/
  ι : Γ →* LineAut
  ι_injective : Function.Injective ι
  ι_dlab : ∀ g, IsDlabLike (ι g)
  /-- The automorphism. -/
  α : Γ ≃* Γ
  /-- The homeomorphism realising `α` by conjugation. -/
  c : LineAut
  α_spec : ∀ g, ι (α g) = c⁻¹ * ι g * c
  /-- A decreasing sequence of fixed points of `c`. -/
  X : ℕ → ℝ
  X_pos : ∀ m, 0 < X m
  X_succ_lt : ∀ m, X (m + 1) < X m
  c_fix : ∀ m, c (X m) = X m
  c_moves : ∀ m y, X (m + 1) < y → y < X m → y < c y
  /-- Nontrivial elements that start moving arbitrarily close to `0`. -/
  supply_small : ∀ τ > 0, ∃ g : Γ, g ≠ 1 ∧ fm (ι g) < τ
  /-- A nontrivial element that only moves points to the right of `X 0`. -/
  supply_top : ∃ g : Γ, g ≠ 1 ∧ X 0 ≤ fm (ι g)
  /-- Noncommuting elements supported in any small interval. -/
  supply_comm : ∀ β γ : ℝ, 0 < β → β < γ → γ ≤ X 0 → ∃ a b : Γ, ∃ p q : ℝ, β < p ∧ q < γ ∧
    (∀ x, x < p → ι a x = x ∧ ι b x = x) ∧ (∀ x, q < x → ι a x = x ∧ ι b x = x) ∧ a * b ≠ b * a

namespace SourceData

variable {Γ : Type*} [Group Γ] (D : SourceData Γ)

/-- The key property of a homomorphism `e`: whenever `e g₀` fixes `(-∞, s]` and `g` starts
moving strictly after `g₀`, then `e g` also fixes `(-∞, s]`. For order-preserving (or
order-reversing) embeddings this is a consequence of convexity, see `Kourovka21149.Order`. -/
def KeyProp (e : Γ →* LineAut) : Prop :=
  ∀ (s : ℝ) (g₀ g : Γ), g₀ ≠ 1 → e g₀ ∈ fixLeft s → fm (D.ι g₀) < fm (D.ι g) → e g ∈ fixLeft s

lemma X_le_X0 (m : ℕ) : D.X m ≤ D.X 0 := by
  induction m with
  | zero => exact le_rfl
  | succ n ih => exact (D.X_succ_lt n).le.trans ih

lemma ι_ne_one {g : Γ} (hg : g ≠ 1) : D.ι g ≠ 1 := by
  intro h
  apply hg
  apply D.ι_injective
  rw [h, map_one]

lemma fm_α {g : Γ} (hg : g ≠ 1) : fm (D.ι (D.α g)) = D.c⁻¹ (fm (D.ι g)) := by
  rw [D.α_spec]
  exact fm_conj D.c (D.ι g) (D.ι_dlab g).idNearBot (D.ι_ne_one hg)

section Levels

variable (e : Γ →* LineAut)

/-- The set of levels `s` such that some nontrivial element starting before `τ` has image
fixing `(-∞, s]`. -/
def S (τ : ℝ) : Set ℝ :=
  {s | ∃ g : Γ, g ≠ 1 ∧ fm (D.ι g) < τ ∧ e g ∈ fixLeft s}

/-- The supremum of `S τ`. -/
noncomputable def w (τ : ℝ) : ℝ := sSup (D.S e τ)

variable {D e}

lemma S_lower {τ s s' : ℝ} (hs : s ∈ D.S e τ) (h : s' ≤ s) : s' ∈ D.S e τ := by
  obtain ⟨g, hg, hfm, hfix⟩ := hs
  exact ⟨g, hg, hfm, fixLeft_anti h hfix⟩

lemma S_mono {τ τ' : ℝ} (h : τ ≤ τ') : D.S e τ ⊆ D.S e τ' := by
  rintro s ⟨g, hg, hfm, hfix⟩
  exact ⟨g, hg, hfm.trans_le h, hfix⟩

lemma key' (hkey : D.KeyProp e) {τ s : ℝ} (hs : s ∈ D.S e τ) {g : Γ}
    (hg : g = 1 ∨ τ ≤ fm (D.ι g)) : e g ∈ fixLeft s := by
  rcases hg with rfl | hg
  · rw [map_one]; exact (fixLeft s).one_mem
  · obtain ⟨g₀, hg₀, hfm, hfix⟩ := hs
    exact hkey s g₀ g hg₀ hfix (hfm.trans_le hg)

lemma S_nonempty (he_dlab : ∀ g, IsDlabLike (e g)) {τ : ℝ} (hτ : 0 < τ) :
    (D.S e τ).Nonempty := by
  obtain ⟨g, hg, hfm⟩ := D.supply_small τ hτ
  obtain ⟨c0, hc0⟩ := (he_dlab g).idNearBot
  exact ⟨c0, g, hg, hfm, hc0⟩

lemma S_bddAbove (he : Function.Injective e) (hkey : D.KeyProp e) {τ : ℝ} (hτ : τ ≤ D.X 0) :
    BddAbove (D.S e τ) := by
  obtain ⟨g, hg, hfm⟩ := D.supply_top
  have hne : e g ≠ 1 := by
    intro h
    apply hg
    apply he
    rw [h, map_one]
  obtain ⟨r, hr⟩ : ∃ r, e g r ≠ r := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_one_iff.mpr hcon)
  refine ⟨r, fun s hs ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  exact hr (key' hkey hs (Or.inr (hτ.trans hfm)) r hlt.le)

lemma w_mono (he : Function.Injective e) (he_dlab : ∀ g, IsDlabLike (e g))
    (hkey : D.KeyProp e) {τ τ' : ℝ} (hτ : 0 < τ) (h : τ ≤ τ') (hτ' : τ' ≤ D.X 0) :
    D.w e τ ≤ D.w e τ' :=
  csSup_le_csSup (S_bddAbove he hkey hτ') (S_nonempty he_dlab hτ) (S_mono h)

/-- If `s < w τ` then `s ∈ S τ`. -/
lemma mem_S_of_lt_w (_he : Function.Injective e) (he_dlab : ∀ g, IsDlabLike (e g))
    (_hkey : D.KeyProp e) {τ s : ℝ} (hτ : 0 < τ) (_hτ' : τ ≤ D.X 0) (hs : s < D.w e τ) :
    s ∈ D.S e τ := by
  obtain ⟨s', hs', hlt⟩ := exists_lt_of_lt_csSup (S_nonempty he_dlab hτ) hs
  exact S_lower hs' hlt.le

lemma le_w_of_mem (he : Function.Injective e) (hkey : D.KeyProp e) {τ s : ℝ}
    (hτ' : τ ≤ D.X 0) (hs : s ∈ D.S e τ) : s ≤ D.w e τ :=
  le_csSup (S_bddAbove he hkey hτ') hs

end Levels

section Transport

variable {e : Γ →* LineAut} {U : LineAut}

lemma S_transport (hu : ∀ f, e (D.α f) = U⁻¹ * e f * U) (τ : ℝ) :
    D.S e (D.c⁻¹ τ) = ⇑(U⁻¹ : LineAut) '' D.S e τ := by
  ext s
  constructor
  · rintro ⟨g', hg', hfm, hfix⟩
    set g := D.α.symm g' with hgdef
    have hαg : D.α g = g' := by simp [hgdef]
    have hg1 : g ≠ 1 := by
      intro h
      apply hg'
      rw [← hαg, h, map_one]
    refine ⟨U s, ⟨g, hg1, ?_, ?_⟩, inv_apply_apply U s⟩
    · rw [← hαg, D.fm_α hg1] at hfm
      exact (D.c⁻¹).strictMono.lt_iff_lt.mp hfm
    · rw [← hαg, hu g] at hfix
      have h' : U⁻¹ * e g * U ∈ fixLeft (U⁻¹ (U s)) := by rwa [inv_apply_apply]
      exact (mem_fixLeft_conj_iff U (e g) (U s)).mp h'
  · rintro ⟨t, ⟨g, hg, hfm, hfix⟩, rfl⟩
    have hg1 : D.α g ≠ 1 := by
      intro h
      apply hg
      apply D.α.injective
      rw [h, map_one]
    refine ⟨D.α g, hg1, ?_, ?_⟩
    · rw [D.fm_α hg]
      exact (D.c⁻¹).strictMono hfm
    · rw [hu g]
      exact (mem_fixLeft_conj_iff U (e g) t).mpr hfix

lemma w_transport (he : Function.Injective e) (he_dlab : ∀ g, IsDlabLike (e g))
    (hkey : D.KeyProp e) (hu : ∀ f, e (D.α f) = U⁻¹ * e f * U) {τ : ℝ} (hτ : 0 < τ)
    (hτ' : τ ≤ D.X 0) : D.w e (D.c⁻¹ τ) = U⁻¹ (D.w e τ) := by
  unfold w
  rw [D.S_transport hu τ]
  exact (OrderIso.map_csSup' U⁻¹ (S_nonempty he_dlab hτ) (S_bddAbove he hkey hτ')).symm

end Transport

section Plateau

variable {e : Γ →* LineAut}

/-- The function `w` has no plateaus. -/
lemma w_ne (he : Function.Injective e) (he_dlab : ∀ g, IsDlabLike (e g)) (hkey : D.KeyProp e)
    {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ) (hγ : γ ≤ D.X 0) : D.w e β ≠ D.w e γ := by
  intro hw
  obtain ⟨a, b, p, q, hp, hq, hlow, hhigh, hab⟩ := D.supply_comm β γ hβ hβγ hγ
  have hpq : p ≤ q := by
    by_contra hlt
    push Not at hlt
    apply hab
    apply D.ι_injective
    rw [map_mul, map_mul]
    apply LineAut.ext_iff'.mpr
    intro x
    rcases lt_or_ge x p with hx | hx
    · simp [mul_apply', (hlow x hx).1, (hlow x hx).2]
    · have hx' : q < x := lt_of_lt_of_le hlt hx
      simp [mul_apply', (hhigh x hx').1, (hhigh x hx').2]
  set sstar := D.w e β with hsstar
  set τ₁ := (β + p) / 2 with hτ₁
  set τ₂ := (q + γ) / 2 with hτ₂
  have hτ₁pos : 0 < τ₁ := by linarith
  have hτ₁γ : τ₁ ≤ D.X 0 := by linarith
  have hτ₂γ : τ₂ ≤ D.X 0 := by linarith
  have hβτ₁ : β ≤ τ₁ := by linarith
  have hτ₁τ₂ : τ₁ ≤ τ₂ := by linarith
  have hτ₂γ' : τ₂ ≤ γ := by linarith
  have hw₁ : D.w e τ₁ = sstar := by
    apply le_antisymm
    · calc D.w e τ₁ ≤ D.w e γ := w_mono he he_dlab hkey hτ₁pos (by linarith) hγ
        _ = sstar := hw.symm
    · exact w_mono he he_dlab hkey hβ hβτ₁ hτ₁γ
  have hw₂ : D.w e τ₂ = sstar := by
    apply le_antisymm
    · calc D.w e τ₂ ≤ D.w e γ := w_mono he he_dlab hkey (by linarith) hτ₂γ' hγ
        _ = sstar := hw.symm
    · calc sstar = D.w e τ₁ := hw₁.symm
        _ ≤ D.w e τ₂ := w_mono he he_dlab hkey hτ₁pos hτ₁τ₂ hτ₂γ
  -- elements supported in `[p, q]` start moving after `τ₁`
  have hstart : ∀ g : Γ, (∀ x, x < p → D.ι g x = x) → g = 1 ∨ τ₁ ≤ fm (D.ι g) := by
    intro g hg
    by_cases h1 : g = 1
    · exact Or.inl h1
    · right
      have := le_fm_of_forall (D.ι_ne_one h1) hg
      linarith
  -- for `s < s*`, the images of `a` and `b` fix `(-∞, s]`
  have hfix_ab : ∀ s < sstar, e a ∈ fixLeft s ∧ e b ∈ fixLeft s := by
    intro s hs
    have hsS : s ∈ D.S e τ₁ :=
      mem_S_of_lt_w he he_dlab hkey hτ₁pos hτ₁γ (by rw [hw₁]; exact hs)
    exact ⟨key' hkey hsS (hstart a fun x hx ↦ (hlow x hx).1),
      key' hkey hsS (hstart b fun x hx ↦ (hlow x hx).2)⟩
  have hfa : ∀ x < sstar, e a x = x := fun x hx ↦ (hfix_ab x hx).1 x le_rfl
  have hfb : ∀ x < sstar, e b x = x := fun x hx ↦ (hfix_ab x hx).2 x le_rfl
  have hfa' : e a sstar = sstar := apply_eq_of_forall_lt (e a) hfa
  have hfb' : e b sstar = sstar := apply_eq_of_forall_lt (e b) hfb
  obtain ⟨ε, hε, hcomm⟩ := commutator_eq_self_near hfa' hfb'
    ((he_dlab a).rightAffine sstar hfa') ((he_dlab b).rightAffine sstar hfb')
  -- the commutator
  set g := a * b * a⁻¹ * b⁻¹ with hgdef
  have hg1 : g ≠ 1 := by
    intro h
    apply hab
    have h' : a * b * a⁻¹ * b⁻¹ = 1 := h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h', one_mul]
  have heg : e g = e a * e b * (e a)⁻¹ * (e b)⁻¹ := by
    simp [hgdef, map_mul, map_inv]
  have hg_fix : e g ∈ fixLeft (sstar + ε / 2) := by
    intro x hx
    rw [heg]
    rcases lt_or_ge x sstar with hxs | hxs
    · show e a (e b ((e a)⁻¹ ((e b)⁻¹ x))) = x
      rw [inv_apply_eq_of_apply_eq (hfb x hxs), inv_apply_eq_of_apply_eq (hfa x hxs), hfb x hxs,
        hfa x hxs]
    · exact hcomm x hxs (by linarith)
  have hg_fm : fm (D.ι g) < τ₂ := by
    have hιg : ∀ x, q < x → D.ι g x = x := by
      intro x hx
      have ha := (hhigh x hx).1
      have hb := (hhigh x hx).2
      simp only [hgdef, map_mul, map_inv, mul_apply']
      rw [inv_apply_eq_of_apply_eq hb, inv_apply_eq_of_apply_eq ha, hb, ha]
    have := fm_le_of_forall (D.ι_ne_one hg1) (D.ι_dlab g).idNearBot hιg
    linarith
  have hmem : sstar + ε / 2 ∈ D.S e τ₂ := ⟨g, hg1, hg_fm, hg_fix⟩
  have := le_w_of_mem he hkey hτ₂γ hmem
  rw [hw₂] at this
  linarith

end Plateau

/-- **Core theorem.** Under the key property, `α` is not induced through `e` by conjugation with
any Dlab-like homeomorphism. -/
theorem false_of_induced (e : Γ →* LineAut) (he : Function.Injective e)
    (he_dlab : ∀ g, IsDlabLike (e g)) (hkey : D.KeyProp e) (U : LineAut) (hU : IsDlabLike U)
    (hu : ∀ f, e (D.α f) = U⁻¹ * e f * U) : False := by
  -- midpoints of the blocks
  set τ : ℕ → ℝ := fun m ↦ (D.X (m + 1) + D.X m) / 2 with hτdef
  have hτ1 : ∀ m, D.X (m + 1) < τ m := fun m ↦ by simp only [hτdef]; linarith [D.X_succ_lt m]
  have hτ2 : ∀ m, τ m < D.X m := fun m ↦ by simp only [hτdef]; linarith [D.X_succ_lt m]
  set β : ℕ → ℝ := fun m ↦ D.c⁻¹ (τ m) with hβdef
  have hcinv_fix : ∀ m, D.c⁻¹ (D.X m) = D.X m := fun m ↦ inv_apply_eq_of_apply_eq (D.c_fix m)
  have hβ1 : ∀ m, D.X (m + 1) < β m := by
    intro m
    have := (D.c⁻¹).strictMono (hτ1 m)
    rwa [hcinv_fix] at this
  have hβ2 : ∀ m, β m < D.X m := by
    intro m
    have := (D.c⁻¹).strictMono (hτ2 m)
    rwa [hcinv_fix] at this
  have hβτ : ∀ m, β m < τ m := by
    intro m
    have := D.c_moves m (β m) (hβ1 m) (hβ2 m)
    simp only [hβdef, apply_inv_apply] at this
    exact this
  have hXpos := D.X_pos
  have hX0 := D.X_le_X0
  -- the points
  set z : ℕ → ℝ := fun m ↦ D.w e (D.X m) with hzdef
  set s : ℕ → ℝ := fun m ↦ D.w e (β m) with hsdef
  have hβpos : ∀ m, 0 < β m := fun m ↦ (hXpos (m + 1)).trans (hβ1 m)
  have hτpos : ∀ m, 0 < τ m := fun m ↦ (hβpos m).trans (hβτ m)
  have hτX0 : ∀ m, τ m ≤ D.X 0 := fun m ↦ (hτ2 m).le.trans (hX0 m)
  have hz : ∀ m, U (z m) = z m := by
    intro m
    have := D.w_transport he he_dlab hkey hu (hXpos m) (hX0 m)
    rw [hcinv_fix] at this
    have h2 := congrArg U this
    rw [apply_inv_apply] at h2
    exact h2
  have hsU : ∀ m, U (s m) = D.w e (τ m) := by
    intro m
    have := D.w_transport he he_dlab hkey hu (hτpos m) (hτX0 m)
    simp only [hsdef, hβdef]
    rw [this, apply_inv_apply]
  have hs : ∀ m, U (s m) ≠ s m := by
    intro m h
    rw [hsU m] at h
    exact D.w_ne he he_dlab hkey (hβpos m) (hβτ m) (hτX0 m) h.symm
  have hle1 : ∀ m, z (m + 1) ≤ s m := fun m ↦
    w_mono he he_dlab hkey (hXpos (m + 1)) (hβ1 m).le ((hβ2 m).le.trans (hX0 m))
  have hle2 : ∀ m, s m ≤ z m := fun m ↦
    w_mono he he_dlab hkey (hβpos m) (hβ2 m).le (hX0 m)
  have h1 : ∀ m, z (m + 1) < s m := by
    intro m
    rcases (hle1 m).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hz (m + 1)) (hs m)
  have h2 : ∀ m, s m < z m := by
    intro m
    rcases (hle2 m).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hz m) (hs m)
  exact no_staircase hU z s hz hs h1 h2

end SourceData

end Kourovka21149

end

/- ## Section: `Ext` -/

section

/-
# Extending interval automorphisms to the real line

Every order automorphism of `[0, 1]` extends by the identity to an order automorphism of `ℝ`.
This gives an injective homomorphism `extHom : Dlab.IntervalAut →* LineAut`. Locally right
`H`-linear interval automorphisms extend to Dlab-like homeomorphisms of `ℝ`, and the
first-disagreement order on `[0, 1]` corresponds to the one on `ℝ`.
-/

open Set
open scoped unitInterval Topology

namespace Kourovka21149

open LineAut

/-- The first-disagreement relation on order automorphisms of `[0, 1]` (Dlab's order). This is the
relation used in the Lean solution of the original Problem 21.149 by Monticone et al. -/
def IntervalFDLt (f g : Dlab.IntervalAut) : Prop :=
  ∃ x : unitInterval, (f x : ℝ) < g x ∧ ∀ y : unitInterval, (g y : ℝ) < f y → (x : ℝ) < y

namespace Ext

variable (f g : Dlab.IntervalAut)

/-- The extension of an interval automorphism by the identity, as a function on `ℝ`. -/
noncomputable def extFun (x : ℝ) : ℝ :=
  if h : x ∈ Icc (0 : ℝ) 1 then (f ⟨x, h⟩ : ℝ) else x

variable {f g}

lemma extFun_of_mem {x : ℝ} (h : x ∈ Icc (0 : ℝ) 1) : extFun f x = f ⟨x, h⟩ := by
  simp [extFun, h]

lemma extFun_of_not_mem {x : ℝ} (h : x ∉ Icc (0 : ℝ) 1) : extFun f x = x := by
  simp [extFun, h]

lemma extFun_coe (x : unitInterval) : extFun f x = f x := by
  rw [extFun_of_mem x.2]

lemma extFun_mem {x : ℝ} (h : x ∈ Icc (0 : ℝ) 1) : extFun f x ∈ Icc (0 : ℝ) 1 := by
  rw [extFun_of_mem h]; exact (f ⟨x, h⟩).2

lemma extFun_strictMono : StrictMono (extFun f) := by
  intro x y hxy
  by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [extFun_of_mem hx, extFun_of_mem hy]
    exact f.strictMono (show (⟨x, hx⟩ : unitInterval) < ⟨y, hy⟩ from hxy)
  · rw [extFun_of_mem hx, extFun_of_not_mem hy]
    have hy1 : 1 < y := by
      by_contra hcon
      exact hy ⟨by linarith [hx.1], not_lt.mp hcon⟩
    exact lt_of_le_of_lt (f ⟨x, hx⟩).2.2 hy1
  · rw [extFun_of_not_mem hx, extFun_of_mem hy]
    have hx0 : x < 0 := by
      by_contra hcon
      exact hx ⟨not_lt.mp hcon, by linarith [hy.2]⟩
    exact lt_of_lt_of_le hx0 (f ⟨y, hy⟩).2.1
  · rw [extFun_of_not_mem hx, extFun_of_not_mem hy]
    exact hxy

lemma extFun_mul (x : ℝ) : extFun (f * g) x = extFun f (extFun g x) := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [extFun_of_mem hx, extFun_of_mem hx, extFun_of_mem (g ⟨x, hx⟩).2]
    rfl
  · rw [extFun_of_not_mem hx, extFun_of_not_mem hx, extFun_of_not_mem hx]

lemma extFun_one (x : ℝ) : extFun (1 : Dlab.IntervalAut) x = x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [extFun_of_mem hx]; rfl
  · rw [extFun_of_not_mem hx]

lemma extFun_surjective : Function.Surjective (extFun f) := by
  intro y
  refine ⟨extFun f⁻¹ y, ?_⟩
  rw [← extFun_mul, mul_inv_cancel, extFun_one]

variable (f)

/-- The extension of an interval automorphism by the identity. -/
noncomputable def ext : LineAut :=
  StrictMono.orderIsoOfSurjective (extFun f) extFun_strictMono extFun_surjective

variable {f}

@[simp] lemma ext_apply (x : ℝ) : ext f x = extFun f x := rfl

lemma ext_mul : ext (f * g) = ext f * ext g := by
  apply RelIso.ext
  intro x
  simp only [ext_apply, mul_apply']
  exact extFun_mul x

lemma ext_one : ext (1 : Dlab.IntervalAut) = 1 := by
  apply RelIso.ext
  intro x
  simp only [ext_apply]
  exact extFun_one x

end Ext

open Ext

/-- Extension by the identity, as a group homomorphism. -/
noncomputable def extHom : Dlab.IntervalAut →* LineAut where
  toFun := Ext.ext
  map_one' := ext_one
  map_mul' _ _ := ext_mul

@[simp] lemma extHom_apply (f : Dlab.IntervalAut) (x : ℝ) : extHom f x = extFun f x := rfl

lemma extHom_apply_coe (f : Dlab.IntervalAut) (x : unitInterval) : extHom f x = f x :=
  extFun_coe x

lemma extHom_apply_of_not_mem (f : Dlab.IntervalAut) {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    extHom f x = x :=
  extFun_of_not_mem hx

lemma extHom_injective : Function.Injective extHom := by
  intro f g h
  apply RelIso.ext
  intro x
  apply Subtype.ext
  have h1 := congrArg (fun a : LineAut ↦ a (x : ℝ)) h
  simp only [extHom_apply, extFun_coe] at h1
  exact h1

lemma extHom_apply_of_nonpos (f : Dlab.IntervalAut) {x : ℝ} (hx : x < 0) : extHom f x = x :=
  extHom_apply_of_not_mem f fun h ↦ absurd h.1 (not_le.mpr hx)

lemma extHom_apply_of_one_le (f : Dlab.IntervalAut) {x : ℝ} (hx : 1 ≤ x) : extHom f x = x := by
  rcases hx.lt_or_eq with hx | rfl
  · exact extHom_apply_of_not_mem f fun h ↦ absurd h.2 (not_le.mpr hx)
  · have h1 : f 1 = 1 := f.map_top
    have h2 := extHom_apply_coe f 1
    rw [h1] at h2
    exact h2

/-- The extension of a locally right `H`-linear interval automorphism is affine to the right of
every point. -/
lemma rightAffineAt_extHom {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut}
    (hf : Dlab.IsLocallyRightHLinear H f) (p : ℝ) : RightAffineAt (extHom f) p := by
  rcases lt_or_ge p 0 with hp | hp
  · refine ⟨-p, by linarith, 1, fun x hx1 hx2 ↦ ?_⟩
    rw [extHom_apply_of_nonpos f (by linarith), extHom_apply_of_nonpos f hp]
    ring
  rcases lt_or_ge p 1 with hp1 | hp1
  · obtain ⟨ε, hε, h, hh⟩ := hf ⟨p, hp, hp1.le⟩ (show (⟨p, hp, hp1.le⟩ : unitInterval) < 1 from hp1)
    refine ⟨min ε (1 - p), lt_min hε (by linarith), Dlab.slopeToReal h.1, fun x hx1 hx2 ↦ ?_⟩
    rcases hx1.lt_or_eq with hx1 | rfl
    · have hx1' : x < 1 := by linarith [min_le_right ε (1 - p)]
      have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hx1'.le⟩
      have := hh (x := ⟨x, hxI⟩) hx1 (by linarith [min_le_left ε (1 - p)])
      rw [extHom_apply_coe f ⟨x, hxI⟩ |>.symm] at this
      rw [show extHom f p = ((f ⟨p, hp, hp1.le⟩ : unitInterval) : ℝ) from
        extHom_apply_coe f ⟨p, hp, hp1.le⟩]
      exact this
    · ring
  · refine ⟨1, one_pos, 1, fun x hx1 _ ↦ ?_⟩
    rw [extHom_apply_of_one_le f (by linarith), extHom_apply_of_one_le f hp1]
    ring

lemma idNearBot_extHom (f : Dlab.IntervalAut) : IdNearBot (extHom f) :=
  ⟨-1, fun x hx ↦ extHom_apply_of_nonpos f (by linarith)⟩

lemma isDlabLike_extHom {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut}
    (hf : Dlab.IsLocallyRightHLinear H f) : IsDlabLike (extHom f) :=
  ⟨idNearBot_extHom f, fun p _ ↦ rightAffineAt_extHom hf p⟩

/-- The first-disagreement order on `[0, 1]` agrees with the one on `ℝ` after extension. -/
lemma intervalFDLt_iff (f g : Dlab.IntervalAut) :
    IntervalFDLt f g ↔ FDLt (extHom f) (extHom g) := by
  constructor
  · rintro ⟨x, hx, hx'⟩
    refine ⟨x, ?_, fun y hy ↦ ?_⟩
    · rwa [extHom_apply_coe, extHom_apply_coe]
    · by_cases hyI : y ∈ Icc (0 : ℝ) 1
      · have := hx' ⟨y, hyI⟩ (by
          rwa [extHom_apply_coe g ⟨y, hyI⟩ |>.symm, extHom_apply_coe f ⟨y, hyI⟩ |>.symm])
        exact this
      · rw [extHom_apply_of_not_mem g hyI, extHom_apply_of_not_mem f hyI] at hy
        exact absurd hy (lt_irrefl _)
  · rintro ⟨x, hx, hx'⟩
    have hxI : x ∈ Icc (0 : ℝ) 1 := by
      by_contra hxI
      rw [extHom_apply_of_not_mem f hxI, extHom_apply_of_not_mem g hxI] at hx
      exact lt_irrefl _ hx
    refine ⟨⟨x, hxI⟩, ?_, fun y hy ↦ ?_⟩
    · rwa [extHom_apply_coe f ⟨x, hxI⟩ |>.symm, extHom_apply_coe g ⟨x, hxI⟩ |>.symm]
    · exact hx' y (by rwa [extHom_apply_coe, extHom_apply_coe])

end Kourovka21149

end

/- ## Section: `Bump` -/

section

/-
# Two-slope bumps

We fix a *slope choice* `S`: a slope subgroup `K = S.K ≤ ℝ_{>0}` together with a slope
`r = S.r ∈ K` with `r > 1` (every nontrivial `K` admits one). For `p < q`, `bumpF p q` is the
piecewise-linear homeomorphism of `ℝ` that is the identity outside `[p, q]`, has slope `r` on an
initial segment of `[p, q]` and slope `1/r` on the rest of `[p, q]`:
`bumpF p q x = max x (min (p + r (x - p)) (q + r⁻¹ (x - q)))`.
For `0 < p < q < 1` it defines an element `bumpAut p q` of Dlab's group `D_K([0,1])`.

We also set up the rank-one slope group `W = ⟨2⟩`, a constructor `mkIntervalAut`, and the
pointwise version `RLin` of local right linearity together with its composition lemma.
-/

open Set
open scoped unitInterval Topology

namespace Kourovka21149

/- ## Slope choices -/

/-- A slope subgroup `K` together with a slope `κ ∈ K` greater than `1`. It is a class so that
the whole construction can be carried out for a fixed but arbitrary choice. -/
class SlopeChoice where
  /-- The slope group. -/
  K : Subgroup NNRealˣ
  /-- A slope in `K` greater than `1`. -/
  κ : NNRealˣ
  mem : κ ∈ K
  one_lt : 1 < Dlab.slopeToReal κ

namespace SlopeChoice

/-- The chosen slope as a real number. -/
noncomputable def r (S : SlopeChoice) : ℝ := Dlab.slopeToReal S.κ

lemma one_lt_r (S : SlopeChoice) : 1 < S.r := S.one_lt

lemma r_pos (S : SlopeChoice) : 0 < S.r := zero_lt_one.trans S.one_lt_r

lemma inv_r_lt_one (S : SlopeChoice) : S.r⁻¹ < 1 := inv_lt_one_of_one_lt₀ S.one_lt_r

lemma inv_r_pos (S : SlopeChoice) : 0 < S.r⁻¹ := inv_pos.mpr S.r_pos

lemma r_mul_inv (S : SlopeChoice) : S.r * S.r⁻¹ = 1 := mul_inv_cancel₀ S.r_pos.ne'

lemma inv_mul_r (S : SlopeChoice) : S.r⁻¹ * S.r = 1 := inv_mul_cancel₀ S.r_pos.ne'

lemma inv_mem (S : SlopeChoice) : S.κ⁻¹ ∈ S.K := S.K.inv_mem S.mem

lemma slope_inv (S : SlopeChoice) : Dlab.slopeToReal S.κ⁻¹ = S.r⁻¹ := by
  simp [r, Dlab.slopeToReal]

/-- Every nontrivial slope group admits a slope choice. -/
lemma exists_of_ne_bot {K : Subgroup NNRealˣ} (hK : K ≠ ⊥) : ∃ S : SlopeChoice, S.K = K := by
  obtain ⟨k, hk, hk1⟩ : ∃ k ∈ K, k ≠ 1 := by
    by_contra h
    push Not at h
    exact hK ((Subgroup.eq_bot_iff_forall K).mpr h)
  have hkr : Dlab.slopeToReal k ≠ 1 := by
    intro h
    apply hk1
    ext
    simpa [Dlab.slopeToReal] using h
  rcases lt_or_gt_of_ne hkr with h | h
  · refine ⟨⟨K, k⁻¹, K.inv_mem hk, ?_⟩, rfl⟩
    have hpos : 0 < Dlab.slopeToReal k := by simp [Dlab.slopeToReal]
    have : Dlab.slopeToReal k⁻¹ = (Dlab.slopeToReal k)⁻¹ := by simp [Dlab.slopeToReal]
    rw [this]
    exact one_lt_inv_iff₀.mpr ⟨hpos, h⟩
  · exact ⟨⟨K, k, hk, h⟩, rfl⟩

end SlopeChoice

/- ## The slope group `⟨2⟩` -/

/-- The slope `2`. -/
noncomputable def twoSlope : NNRealˣ := Units.mk0 (2 : NNReal) (by norm_num)

/-- The rank-one slope group `⟨2⟩ ≤ ℝ_{>0}`. -/
noncomputable def W : Subgroup NNRealˣ := Subgroup.zpowers twoSlope

lemma twoSlope_mem : twoSlope ∈ W := Subgroup.mem_zpowers _

lemma slope_one : Dlab.slopeToReal (1 : NNRealˣ) = 1 := by simp [Dlab.slopeToReal]

lemma slope_two : Dlab.slopeToReal twoSlope = 2 := by simp [Dlab.slopeToReal, twoSlope]

/-- The slope choice `(⟨2⟩, 2)`. -/
@[instance_reducible]
noncomputable def SlopeChoice.two : SlopeChoice where
  K := W
  κ := twoSlope
  mem := twoSlope_mem
  one_lt := by rw [slope_two]; norm_num

lemma W_ne_bot : W ≠ ⊥ := by
  intro h
  have : twoSlope = 1 := (Subgroup.eq_bot_iff_forall W).mp h _ twoSlope_mem
  have h2 := congrArg Dlab.slopeToReal this
  rw [slope_two, slope_one] at h2
  norm_num at h2

section RealRLin

variable [S : SlopeChoice]

/-- A real function whose right germ at `a` is affine with slope in `K`. -/
def RealRLin (F : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ ε > 0, ∃ s : NNRealˣ, s ∈ S.K ∧
    ∀ x, a < x → x < a + ε → F x = F a + Dlab.slopeToReal s * (x - a)

lemma realRLin_of_eq {F : ℝ → ℝ} {a ε : ℝ} (hε : 0 < ε) (k : NNRealˣ) (hk : k ∈ S.K)
    (h : ∀ x, a < x → x < a + ε → F x = F a + Dlab.slopeToReal k * (x - a)) : RealRLin F a :=
  ⟨ε, hε, k, hk, h⟩

end RealRLin

/- ## Interval automorphisms from real functions -/

/-- Build an interval automorphism from a pair of inverse real functions. -/
noncomputable def mkIntervalAut (fR gR : ℝ → ℝ)
    (hf_maps : ∀ x, x ∈ Icc (0 : ℝ) 1 → fR x ∈ Icc (0 : ℝ) 1)
    (hg_maps : ∀ y, y ∈ Icc (0 : ℝ) 1 → gR y ∈ Icc (0 : ℝ) 1)
    (hfg : ∀ x, x ∈ Icc (0 : ℝ) 1 → gR (fR x) = x)
    (hgf : ∀ y, y ∈ Icc (0 : ℝ) 1 → fR (gR y) = y)
    (hmono : StrictMonoOn fR (Icc (0 : ℝ) 1)) : Dlab.IntervalAut where
  toEquiv :=
    { toFun := fun x ↦ ⟨fR x, hf_maps x x.2⟩
      invFun := fun y ↦ ⟨gR y, hg_maps y y.2⟩
      left_inv := fun x ↦ Subtype.ext (hfg x x.2)
      right_inv := fun y ↦ Subtype.ext (hgf y y.2) }
  map_rel_iff' := by
    intro a b
    exact (show StrictMono (fun x : unitInterval ↦ fR x) from
      fun x y hxy ↦ hmono x.2 y.2 hxy).le_iff_le

/-- Pointwise local right linearity with slopes in `H`. -/
def RLin (H : Subgroup NNRealˣ) (f : Dlab.IntervalAut) (a : unitInterval) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ h : H, ∀ ⦃x : unitInterval⦄, (a : ℝ) < x → (x : ℝ) < (a : ℝ) + ε →
    (f x : ℝ) = (f a : ℝ) + Dlab.slopeToReal h.1 * ((x : ℝ) - (a : ℝ))

lemma isLocallyRightHLinear_iff {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut} :
    Dlab.IsLocallyRightHLinear H f ↔ ∀ a : unitInterval, a < 1 → RLin H f a := Iff.rfl

lemma RLin.mul {H : Subgroup NNRealˣ} {f g : Dlab.IntervalAut} {a : unitInterval}
    (hg : RLin H g a) (hf : RLin H f (g a)) : RLin H (f * g) a := by
  obtain ⟨ε₁, hε₁, h₁, hh₁⟩ := hg
  obtain ⟨ε₂, hε₂, h₂, hh₂⟩ := hf
  have h₁_pos : 0 < Dlab.slopeToReal h₁.1 := by simp [Dlab.slopeToReal]
  refine ⟨min ε₁ (ε₂ / Dlab.slopeToReal h₁.1), lt_min hε₁ (div_pos hε₂ h₁_pos), h₂ * h₁,
    fun x hx₁ hx₂ ↦ ?_⟩
  have hg_eq := hh₁ hx₁ (by linarith [min_le_left ε₁ (ε₂ / Dlab.slopeToReal h₁.1)])
  have hf_eq :=
    hh₂ (g.strictMono hx₁) (by
      nlinarith [min_le_right ε₁ (ε₂ / Dlab.slopeToReal h₁.1),
        mul_div_cancel₀ ε₂ (ne_of_gt h₁_pos)])
  simp only [RelIso.mul_apply, Dlab.slopeToReal, Subgroup.coe_mul, Units.val_mul,
    NNReal.coe_mul] at hg_eq hf_eq ⊢
  rw [hf_eq, hg_eq]
  ring

lemma RLin.of_real [S : SlopeChoice] {H : Subgroup NNRealˣ} (hW : S.K ≤ H)
    {f : Dlab.IntervalAut} {F : ℝ → ℝ} (hF : ∀ x : unitInterval, (f x : ℝ) = F x)
    {a : unitInterval} (h : RealRLin F a) : RLin H f a := by
  obtain ⟨ε, hε, s, hs, hh⟩ := h
  refine ⟨ε, hε, ⟨s, hW hs⟩, fun x hx₁ hx₂ ↦ ?_⟩
  rw [hF x, hF a]
  exact hh x hx₁ hx₂

/-- An interval automorphism that is the identity on `[0, δ)` is right linear at `0`. -/
lemma RLin.zero_of_id {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : unitInterval, (x : ℝ) < δ → f x = x) : RLin H f 0 := by
  refine ⟨δ, hδ, 1, fun x hx₁ hx₂ ↦ ?_⟩
  have h0 : f 0 = 0 := f.map_bot
  rw [h x (by simpa using hx₂), h0]
  simp [Dlab.slopeToReal]

lemma isIdentityNearZero_of {f : Dlab.IntervalAut} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : unitInterval, (x : ℝ) < δ → f x = x) : Dlab.IsIdentityNearZero f := by
  have hs : {x : unitInterval | (x : ℝ) < δ} ∈ 𝓝 (0 : unitInterval) :=
    IsOpen.mem_nhds (isOpen_lt continuous_subtype_val continuous_const) (by simpa using hδ)
  filter_upwards [hs] with x hx
  exact h x hx

lemma isIdentityNearOne_of {f : Dlab.IntervalAut} {δ : ℝ} (hδ : δ < 1)
    (h : ∀ x : unitInterval, δ < (x : ℝ) → f x = x) : Dlab.IsIdentityNearOne f := by
  have hs : {x : unitInterval | δ < (x : ℝ)} ∈ 𝓝 (1 : unitInterval) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_subtype_val) (by simpa using hδ)
  filter_upwards [hs] with x hx
  exact h x hx

lemma exists_id_near_zero {f : Dlab.IntervalAut} (hf : Dlab.IsIdentityNearZero f) :
    ∃ δ > 0, ∀ x : unitInterval, (x : ℝ) < δ → f x = x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hf
  refine ⟨ε, hε, fun x hx ↦ hball ?_⟩
  change dist x 0 < ε
  rw [Subtype.dist_eq]
  simp only [Set.Icc.coe_zero, sub_zero, Real.dist_eq]
  rw [abs_of_nonneg x.2.1]
  exact hx

lemma exists_id_near_one {f : Dlab.IntervalAut} (hf : Dlab.IsIdentityNearOne f) :
    ∃ δ < 1, ∀ x : unitInterval, δ < (x : ℝ) → f x = x := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hf
  refine ⟨1 - ε, by linarith, fun x hx ↦ hball ?_⟩
  change dist x 1 < ε
  rw [Subtype.dist_eq]
  simp only [Set.Icc.coe_one, Real.dist_eq]
  rw [abs_of_nonpos (by linarith [x.2.2])]
  linarith

/- ## Scalings, and inverses of their maxima and minima -/

/-- The scaling by the factor `k` about the point `c`. -/
def sc (c k x : ℝ) : ℝ := c + k * (x - c)

lemma sc_strictMono {c k : ℝ} (hk : 0 < k) : StrictMono (sc c k) := fun a b hab ↦ by
  unfold sc
  have := mul_lt_mul_of_pos_left (sub_lt_sub_right hab c) hk
  linarith

lemma sc_sc {c k k' : ℝ} (hk : k * k' = 1) (x : ℝ) : sc c k (sc c k' x) = x := by
  unfold sc
  have : k * (c + k' * (x - c) - c) = (k * k') * (x - c) := by ring
  rw [this, hk]
  ring

lemma sc_apply_eq (c k a x : ℝ) : sc c k x = sc c k a + k * (x - a) := by unfold sc; ring

lemma strictMono_min' {u v : ℝ → ℝ} (hu : StrictMono u) (hv : StrictMono v) :
    StrictMono fun x ↦ min (u x) (v x) := fun _ _ hab ↦
  lt_min (min_lt_of_left_lt (hu hab)) (min_lt_of_right_lt (hv hab))

lemma strictMono_max' {u v : ℝ → ℝ} (hu : StrictMono u) (hv : StrictMono v) :
    StrictMono fun x ↦ max (u x) (v x) := fun _ _ hab ↦
  max_lt (lt_max_of_lt_left (hu hab)) (lt_max_of_lt_right (hv hab))

lemma monotone_of_inv {u u' : ℝ → ℝ} (hu : StrictMono u) (hu'' : ∀ y, u (u' y) = y) :
    Monotone u' := fun a b hab ↦ by
  rw [← hu.le_iff_le, hu'', hu'']
  exact hab

section MaxMin

variable {u v u' v' : ℝ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
  (hu' : ∀ x, u' (u x) = x) (hv' : ∀ x, v' (v x) = x)
  (hu'' : ∀ y, u (u' y) = y) (hv'' : ∀ y, v (v' y) = y)
include hu hv hu' hv' hu'' hv''

/-- The inverse of `min u v` is `max u' v'`. -/
lemma max_inv_min (x : ℝ) : max (u' (min (u x) (v x))) (v' (min (u x) (v x))) = x := by
  rcases le_total (u x) (v x) with h | h
  · rw [min_eq_left h, hu']
    exact max_eq_left (by simpa [hv'] using monotone_of_inv hv hv'' h)
  · rw [min_eq_right h, hv']
    exact max_eq_right (by simpa [hu'] using monotone_of_inv hu hu'' h)

omit hu' hv' in
lemma min_max_inv (y : ℝ) : min (u (max (u' y) (v' y))) (v (max (u' y) (v' y))) = y := by
  rcases le_total (u' y) (v' y) with h | h
  · rw [max_eq_right h, hv'']
    exact min_eq_right (by simpa [hu''] using hu.monotone h)
  · rw [max_eq_left h, hu'']
    exact min_eq_left (by simpa [hv''] using hv.monotone h)

/-- The inverse of `max u v` is `min u' v'`. -/
lemma min_inv_max (x : ℝ) : min (u' (max (u x) (v x))) (v' (max (u x) (v x))) = x := by
  rcases le_total (u x) (v x) with h | h
  · rw [max_eq_right h, hv']
    exact min_eq_right (by simpa [hu'] using monotone_of_inv hu hu'' h)
  · rw [max_eq_left h, hu']
    exact min_eq_left (by simpa [hv'] using monotone_of_inv hv hv'' h)

omit hu' hv' in
lemma max_min_inv (y : ℝ) : max (u (min (u' y) (v' y))) (v (min (u' y) (v' y))) = y := by
  rcases le_total (u' y) (v' y) with h | h
  · rw [min_eq_left h, hu'']
    exact max_eq_left (by simpa [hv''] using hv.monotone h)
  · rw [min_eq_right h, hv'']
    exact max_eq_right (by simpa [hu''] using hu.monotone h)

end MaxMin

/- ## Bump functions -/

section BumpFun

variable [S : SlopeChoice] {p q : ℝ}

/-- The two-slope bump on `[p, q]`: slope `r`, then slope `1/r`. -/
noncomputable def bumpF (p q x : ℝ) : ℝ := max x (min (sc p S.r x) (sc q S.r⁻¹ x))

/-- The inverse of `bumpF p q`. -/
noncomputable def bumpInvF (p q y : ℝ) : ℝ := min y (max (sc p S.r⁻¹ y) (sc q S.r y))

lemma bump_min_strictMono : StrictMono fun x ↦ min (sc p S.r x) (sc q S.r⁻¹ x) :=
  strictMono_min' (sc_strictMono S.r_pos) (sc_strictMono S.inv_r_pos)

lemma bump_max_strictMono : StrictMono fun y ↦ max (sc p S.r⁻¹ y) (sc q S.r y) :=
  strictMono_max' (sc_strictMono S.inv_r_pos) (sc_strictMono S.r_pos)

lemma bump_max_min (x : ℝ) :
    max (sc p S.r⁻¹ (min (sc p S.r x) (sc q S.r⁻¹ x)))
      (sc q S.r (min (sc p S.r x) (sc q S.r⁻¹ x))) = x :=
  max_inv_min (sc_strictMono S.r_pos) (sc_strictMono S.inv_r_pos) (sc_sc S.inv_mul_r)
    (sc_sc S.r_mul_inv) (sc_sc S.r_mul_inv) (sc_sc S.inv_mul_r) x

lemma bump_min_max (y : ℝ) :
    min (sc p S.r (max (sc p S.r⁻¹ y) (sc q S.r y)))
      (sc q S.r⁻¹ (max (sc p S.r⁻¹ y) (sc q S.r y))) = y :=
  min_max_inv (sc_strictMono S.r_pos) (sc_strictMono S.inv_r_pos) (sc_sc S.r_mul_inv)
    (sc_sc S.inv_mul_r) y

lemma bumpF_strictMono (_hpq : p < q) : StrictMono (bumpF p q) :=
  strictMono_max' strictMono_id bump_min_strictMono

lemma bumpInvF_strictMono (_hpq : p < q) : StrictMono (bumpInvF p q) :=
  strictMono_min' strictMono_id bump_max_strictMono

lemma bumpInvF_bumpF (_hpq : p < q) (x : ℝ) : bumpInvF p q (bumpF p q x) = x :=
  min_inv_max (u := id) (v := fun x ↦ min (sc p S.r x) (sc q S.r⁻¹ x)) (u' := id)
    (v' := fun y ↦ max (sc p S.r⁻¹ y) (sc q S.r y)) strictMono_id bump_min_strictMono
    (fun _ ↦ rfl) bump_max_min (fun _ ↦ rfl) bump_min_max x

lemma bumpF_bumpInvF (_hpq : p < q) (y : ℝ) : bumpF p q (bumpInvF p q y) = y :=
  max_min_inv (u := id) (v := fun x ↦ min (sc p S.r x) (sc q S.r⁻¹ x)) (u' := id)
    (v' := fun y ↦ max (sc p S.r⁻¹ y) (sc q S.r y)) strictMono_id bump_min_strictMono
    (fun _ ↦ rfl) bump_min_max y

lemma bumpF_of_le {x : ℝ} (hx : x ≤ p) : bumpF p q x = x := by
  have h : sc p S.r x ≤ x := by
    have e : sc p S.r x = x - (S.r - 1) * (p - x) := by unfold sc; ring
    have : 0 ≤ (S.r - 1) * (p - x) := mul_nonneg (by linarith [S.one_lt_r]) (by linarith)
    linarith
  exact max_eq_left ((min_le_left _ _).trans h)

lemma bumpF_of_ge (_hpq : p < q) {x : ℝ} (hx : q ≤ x) : bumpF p q x = x := by
  have h : sc q S.r⁻¹ x ≤ x := by
    have e : sc q S.r⁻¹ x = x - (1 - S.r⁻¹) * (x - q) := by unfold sc; ring
    have : 0 ≤ (1 - S.r⁻¹) * (x - q) := mul_nonneg (by linarith [S.inv_r_lt_one]) (by linarith)
    linarith
  exact max_eq_left ((min_le_right _ _).trans h)

lemma lt_bumpF {x : ℝ} (hx1 : p < x) (hx2 : x < q) : x < bumpF p q x := by
  have h1 : x < sc p S.r x := by
    have e : sc p S.r x = x + (S.r - 1) * (x - p) := by unfold sc; ring
    have : 0 < (S.r - 1) * (x - p) := mul_pos (by linarith [S.one_lt_r]) (by linarith)
    linarith
  have h2 : x < sc q S.r⁻¹ x := by
    have e : sc q S.r⁻¹ x = x + (1 - S.r⁻¹) * (q - x) := by unfold sc; ring
    have : 0 < (1 - S.r⁻¹) * (q - x) := mul_pos (by linarith [S.inv_r_lt_one]) (by linarith)
    linarith
  exact lt_max_of_lt_right (lt_min h1 h2)

lemma le_bumpF (_hpq : p < q) : ∀ x, x ≤ bumpF p q x := fun _ ↦ le_max_left _ _

lemma bumpInvF_le (_hpq : p < q) : ∀ y, bumpInvF p q y ≤ y := fun _ ↦ min_le_left _ _

lemma bumpInvF_of_le {y : ℝ} (hy : y ≤ p) : bumpInvF p q y = y := by
  have h : y ≤ sc p S.r⁻¹ y := by
    have e : sc p S.r⁻¹ y = y + (1 - S.r⁻¹) * (p - y) := by unfold sc; ring
    have : 0 ≤ (1 - S.r⁻¹) * (p - y) := mul_nonneg (by linarith [S.inv_r_lt_one]) (by linarith)
    linarith
  exact min_eq_left (h.trans (le_max_left _ _))

lemma bumpInvF_of_ge {y : ℝ} (hy : q ≤ y) : bumpInvF p q y = y := by
  have h : y ≤ sc q S.r y := by
    have e : sc q S.r y = y + (S.r - 1) * (y - q) := by unfold sc; ring
    have : 0 ≤ (S.r - 1) * (y - q) := mul_nonneg (by linarith [S.one_lt_r]) (by linarith)
    linarith
  exact min_eq_left (h.trans (le_max_right _ _))

lemma bumpF_mem_Ico (hpq : p < q) {x : ℝ} (hx : x ∈ Ico p q) : bumpF p q x ∈ Ico p q := by
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨hx0.trans (le_bumpF hpq x), ?_⟩
  calc bumpF p q x < bumpF p q q := bumpF_strictMono hpq hx1
    _ = q := bumpF_of_ge hpq le_rfl

lemma bumpInvF_mem_Ico (hpq : p < q) {y : ℝ} (hy : y ∈ Ico p q) : bumpInvF p q y ∈ Ico p q := by
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, lt_of_le_of_lt (bumpInvF_le hpq y) hy1⟩
  calc p = bumpInvF p q p := (bumpInvF_of_le le_rfl).symm
    _ ≤ bumpInvF p q y := (bumpInvF_strictMono hpq).monotone hy0

lemma bumpInvF_ge (hpq : p < q) {y : ℝ} (hy : p ≤ y) : p ≤ bumpInvF p q y := by
  calc p = bumpInvF p q p := (bumpInvF_of_le le_rfl).symm
    _ ≤ bumpInvF p q y := (bumpInvF_strictMono hpq).monotone hy

lemma bumpF_mem_Icc (_hp : 0 ≤ p) (hpq : p < q) (hq : q ≤ 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    bumpF p q x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨hx0.trans (le_bumpF hpq x), ?_⟩
  rcases lt_or_ge x q with hxq | hxq
  · have := bumpF_strictMono hpq hxq
    rw [bumpF_of_ge hpq le_rfl] at this
    linarith
  · rw [bumpF_of_ge hpq hxq]; exact hx1

lemma bumpInvF_mem_Icc (hp : 0 ≤ p) (hpq : p < q) (_hq : q ≤ 1) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) : bumpInvF p q y ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, (bumpInvF_le hpq y).trans hy1⟩
  rcases le_or_gt y p with hyp | hyp
  · rw [bumpInvF_of_le hyp]; exact hy0
  · calc (0 : ℝ) ≤ p := hp
      _ = bumpInvF p q p := (bumpInvF_of_le le_rfl).symm
      _ ≤ bumpInvF p q y := (bumpInvF_strictMono hpq).monotone hyp.le

lemma bumpF_realRLin (_hpq : p < q) (a : ℝ) : RealRLin (bumpF p q) a := by
  rcases lt_or_ge a p with ha | ha
  · refine realRLin_of_eq (ε := p - a) (by linarith) 1 S.K.one_mem fun x hx1 hx2 ↦ ?_
    rw [slope_one, bumpF_of_le (by linarith), bumpF_of_le ha.le]
    ring
  rcases lt_or_ge a q with hq | hq
  swap
  · refine realRLin_of_eq (ε := 1) one_pos 1 S.K.one_mem fun x hx1 hx2 ↦ ?_
    rw [slope_one, bumpF_of_ge _hpq (by linarith), bumpF_of_ge _hpq hq]
    ring
  -- `p ≤ a < q`
  set d : ℝ := sc p S.r a - sc q S.r⁻¹ a with hd
  have hdiff : ∀ x, sc p S.r x - sc q S.r⁻¹ x = d + (S.r - S.r⁻¹) * (x - a) := by
    intro x; simp only [hd, sc]; ring
  have hrr : 0 < S.r - S.r⁻¹ := by linarith [S.one_lt_r, S.inv_r_lt_one]
  rcases lt_or_ge d 0 with hd0 | hd0
  · -- the first piece, slope `r`
    have hpiece : ∀ x, a ≤ x → x < a + (-d) / (S.r - S.r⁻¹) → bumpF p q x = sc p S.r x := by
      intro x hx1 hx2
      have h1 : sc p S.r x ≤ sc q S.r⁻¹ x := by
        have := hdiff x
        have : (x - a) * (S.r - S.r⁻¹) < -d :=
          (lt_div_iff₀ hrr).mp (by linarith : x - a < (-d) / (S.r - S.r⁻¹))
        nlinarith
      have h2 : x ≤ sc p S.r x := by
        have e : sc p S.r x = x + (S.r - 1) * (x - p) := by unfold sc; ring
        have : 0 ≤ (S.r - 1) * (x - p) := mul_nonneg (by linarith [S.one_lt_r]) (by linarith)
        linarith
      unfold bumpF
      rw [min_eq_left h1, max_eq_right h2]
    have hε : 0 < (-d) / (S.r - S.r⁻¹) := div_pos (by linarith) hrr
    refine realRLin_of_eq hε S.κ S.mem fun x hx1 hx2 ↦ ?_
    rw [hpiece x hx1.le hx2, hpiece a le_rfl (by linarith)]
    exact sc_apply_eq p S.r a x
  · -- the second piece, slope `1/r`
    have hpiece : ∀ x, a ≤ x → x ≤ q → bumpF p q x = sc q S.r⁻¹ x := by
      intro x hx1 hx2
      have h1 : sc q S.r⁻¹ x ≤ sc p S.r x := by
        have := hdiff x
        have : 0 ≤ (S.r - S.r⁻¹) * (x - a) := mul_nonneg hrr.le (by linarith)
        linarith
      have h2 : x ≤ sc q S.r⁻¹ x := by
        have e : sc q S.r⁻¹ x = x + (1 - S.r⁻¹) * (q - x) := by unfold sc; ring
        have : 0 ≤ (1 - S.r⁻¹) * (q - x) :=
          mul_nonneg (by linarith [S.inv_r_lt_one]) (by linarith)
        linarith
      unfold bumpF
      rw [min_eq_right h1, max_eq_right h2]
    refine realRLin_of_eq (ε := q - a) (by linarith) S.κ⁻¹ S.inv_mem fun x hx1 hx2 ↦ ?_
    rw [hpiece x hx1.le (by linarith), hpiece a le_rfl hq.le, S.slope_inv]
    exact sc_apply_eq q S.r⁻¹ a x

lemma bumpInvF_realRLin (_hpq : p < q) (a : ℝ) : RealRLin (bumpInvF p q) a := by
  rcases lt_or_ge a p with ha | ha
  · refine realRLin_of_eq (ε := p - a) (by linarith) 1 S.K.one_mem fun x hx1 hx2 ↦ ?_
    rw [slope_one, bumpInvF_of_le (by linarith), bumpInvF_of_le ha.le]
    ring
  rcases lt_or_ge a q with hq | hq
  swap
  · refine realRLin_of_eq (ε := 1) one_pos 1 S.K.one_mem fun x hx1 hx2 ↦ ?_
    rw [slope_one, bumpInvF_of_ge (by linarith), bumpInvF_of_ge hq]
    ring
  -- `p ≤ a < q`
  set d : ℝ := sc q S.r a - sc p S.r⁻¹ a with hd
  have hdiff : ∀ x, sc q S.r x - sc p S.r⁻¹ x = d + (S.r - S.r⁻¹) * (x - a) := by
    intro x; simp only [hd, sc]; ring
  have hrr : 0 < S.r - S.r⁻¹ := by linarith [S.one_lt_r, S.inv_r_lt_one]
  rcases lt_or_ge d 0 with hd0 | hd0
  · -- the first piece, slope `1/r`
    have hpiece : ∀ x, a ≤ x → x < a + (-d) / (S.r - S.r⁻¹) →
        bumpInvF p q x = sc p S.r⁻¹ x := by
      intro x hx1 hx2
      have h1 : sc q S.r x ≤ sc p S.r⁻¹ x := by
        have := hdiff x
        have : (x - a) * (S.r - S.r⁻¹) < -d :=
          (lt_div_iff₀ hrr).mp (by linarith : x - a < (-d) / (S.r - S.r⁻¹))
        nlinarith
      have h2 : sc p S.r⁻¹ x ≤ x := by
        have e : sc p S.r⁻¹ x = x - (1 - S.r⁻¹) * (x - p) := by unfold sc; ring
        have : 0 ≤ (1 - S.r⁻¹) * (x - p) :=
          mul_nonneg (by linarith [S.inv_r_lt_one]) (by linarith)
        linarith
      unfold bumpInvF
      rw [max_eq_left h1, min_eq_right h2]
    have hε : 0 < (-d) / (S.r - S.r⁻¹) := div_pos (by linarith) hrr
    refine realRLin_of_eq hε S.κ⁻¹ S.inv_mem fun x hx1 hx2 ↦ ?_
    rw [hpiece x hx1.le hx2, hpiece a le_rfl (by linarith), S.slope_inv]
    exact sc_apply_eq p S.r⁻¹ a x
  · -- the second piece, slope `r`
    have hpiece : ∀ x, a ≤ x → x ≤ q → bumpInvF p q x = sc q S.r x := by
      intro x hx1 hx2
      have h1 : sc p S.r⁻¹ x ≤ sc q S.r x := by
        have := hdiff x
        have : 0 ≤ (S.r - S.r⁻¹) * (x - a) := mul_nonneg hrr.le (by linarith)
        linarith
      have h2 : sc q S.r x ≤ x := by
        have e : sc q S.r x = x - (S.r - 1) * (q - x) := by unfold sc; ring
        have : 0 ≤ (S.r - 1) * (q - x) := mul_nonneg (by linarith [S.one_lt_r]) (by linarith)
        linarith
      unfold bumpInvF
      rw [max_eq_right h1, min_eq_right h2]
    refine realRLin_of_eq (ε := q - a) (by linarith) S.κ S.mem fun x hx1 hx2 ↦ ?_
    rw [hpiece x hx1.le (by linarith), hpiece a le_rfl hq.le]
    exact sc_apply_eq q S.r a x

/-- The displacement of a bump is bounded below on `[p, q]`. -/
lemma bumpF_sub_ge (y : ℝ) :
    min ((S.r - 1) * (y - p)) ((1 - S.r⁻¹) * (q - y)) ≤ bumpF p q y - y := by
  have e1 : sc p S.r y - y = (S.r - 1) * (y - p) := by unfold sc; ring
  have e2 : sc q S.r⁻¹ y - y = (1 - S.r⁻¹) * (q - y) := by unfold sc; ring
  change _ ≤ max y (min (sc p S.r y) (sc q S.r⁻¹ y)) - y
  rcases min_cases (sc p S.r y) (sc q S.r⁻¹ y) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
    linarith [le_max_right y (sc p S.r y),
      min_le_left ((S.r - 1) * (y - p)) ((1 - S.r⁻¹) * (q - y))]
  · rw [h1]
    linarith [le_max_right y (sc q S.r⁻¹ y),
      min_le_right ((S.r - 1) * (y - p)) ((1 - S.r⁻¹) * (q - y))]

/-- The displacement of an inverse bump is bounded below on `[p, q]`. -/
lemma bumpInvF_sub_ge (y : ℝ) :
    min ((1 - S.r⁻¹) * (y - p)) ((S.r - 1) * (q - y)) ≤ y - bumpInvF p q y := by
  have e1 : y - sc p S.r⁻¹ y = (1 - S.r⁻¹) * (y - p) := by unfold sc; ring
  have e2 : y - sc q S.r y = (S.r - 1) * (q - y) := by unfold sc; ring
  change _ ≤ y - min y (max (sc p S.r⁻¹ y) (sc q S.r y))
  rcases max_cases (sc p S.r⁻¹ y) (sc q S.r y) with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1]
    linarith [min_le_right y (sc p S.r⁻¹ y),
      min_le_left ((1 - S.r⁻¹) * (y - p)) ((S.r - 1) * (q - y))]
  · rw [h1]
    linarith [min_le_right y (sc q S.r y),
      min_le_right ((1 - S.r⁻¹) * (y - p)) ((S.r - 1) * (q - y))]

end BumpFun

/- ## Bumps as elements of `D_K([0,1])` -/

section BumpAut

variable [S : SlopeChoice] {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1)
include hp hpq hq

/-- The bump on `[p, q]` as an interval automorphism. -/
noncomputable def bumpAut : Dlab.IntervalAut :=
  mkIntervalAut (bumpF p q) (bumpInvF p q) (fun _ hx ↦ bumpF_mem_Icc hp.le hpq hq.le hx)
    (fun _ hy ↦ bumpInvF_mem_Icc hp.le hpq hq.le hy) (fun x _ ↦ bumpInvF_bumpF hpq x)
    (fun y _ ↦ bumpF_bumpInvF hpq y) ((bumpF_strictMono hpq).strictMonoOn _)

lemma bumpAut_apply (x : unitInterval) : (bumpAut hp hpq hq x : ℝ) = bumpF p q x := rfl

lemma bumpAut_isElement : Dlab.IsElement S.K (bumpAut hp hpq hq) := by
  refine ⟨fun a _ ↦ RLin.of_real le_rfl (bumpAut_apply hp hpq hq) (bumpF_realRLin hpq a),
    isIdentityNearZero_of hp fun x hx ↦ Subtype.ext ?_,
    isIdentityNearOne_of hq fun x hx ↦ Subtype.ext ?_⟩
  · rw [bumpAut_apply]; exact bumpF_of_le hx.le
  · rw [bumpAut_apply]; exact bumpF_of_ge hpq hx.le

lemma extHom_bumpAut (x : ℝ) : extHom (bumpAut hp hpq hq) x = bumpF p q x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have := extHom_apply_coe (bumpAut hp hpq hq) ⟨x, hx⟩
    rw [this, bumpAut_apply]
  · rw [extHom_apply_of_not_mem _ hx]
    rcases not_and_or.mp hx with hx0 | hx1
    · exact (bumpF_of_le (by linarith [not_le.mp hx0])).symm
    · exact (bumpF_of_ge hpq (by linarith [not_le.mp hx1])).symm

end BumpAut

end Kourovka21149

end

/- ## Section: `Conj` -/

section

/-
# The conjugating homeomorphism `h` and the automorphism `α`

Let `ℓ(x) = 2 ^ ⌊log₂ x⌋`, so that `x` lies in the dyadic block `[ℓ(x), 2ℓ(x))`. The
homeomorphism `h = hF` is the identity outside `(0, 1)`, equals the two-slope bump on every dyadic
block `[2^{-m-2}, 2^{-m-1})` near `0`, and on every block `[1 - 2^{-m-1}, 1 - 2^{-m-2})` near `1`.
Its support components accumulate at both `0` and `1`, so `h` lies in no Dlab group, but
conjugation by `h` preserves `D_K([0,1])`. This gives the automorphism
`α : DlabGroup K ≃* DlabGroup K`, `α f = h⁻¹ f h` (as in Gong–Yang–Zeng, arXiv:2609.18630, where
`K = ⟨2⟩`). Here `K` and the slope `r > 1` of the bumps come from a `SlopeChoice`.
-/

open Set
open scoped unitInterval Topology

namespace Kourovka21149

/- ## Dyadic blocks -/

/-- `ell x = 2 ^ ⌊log₂ x⌋`. -/
noncomputable def ell (x : ℝ) : ℝ := (2 : ℝ) ^ (Int.log 2 x)

lemma ell_pos (x : ℝ) : 0 < ell x := zpow_pos (by norm_num) _

lemma ell_le {x : ℝ} (hx : 0 < x) : ell x ≤ x := by
  have := Int.zpow_log_le_self (R := ℝ) (b := 2) (by norm_num) hx
  simpa [ell] using this

lemma lt_two_mul_ell (x : ℝ) : x < 2 * ell x := by
  have := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) (by norm_num) x
  simp only [Nat.cast_ofNat] at this
  rw [zpow_add_one₀ two_ne_zero] at this
  unfold ell
  linarith

lemma ell_eq_of_mem {x y : ℝ} (hy1 : ell x ≤ y) (hy2 : y < 2 * ell x) : ell y = ell x := by
  have hy : 0 < y := lt_of_lt_of_le (ell_pos x) hy1
  have h1 : Int.log 2 x ≤ Int.log 2 y := by
    refine (Int.zpow_le_iff_le_log (R := ℝ) (b := 2) (by norm_num) hy).mp ?_
    simpa [ell] using hy1
  have h2 : Int.log 2 y < Int.log 2 x + 1 := by
    refine (Int.lt_zpow_iff_log_lt (R := ℝ) (b := 2) (by norm_num) hy).mp ?_
    simp only [Nat.cast_ofNat]
    rw [zpow_add_one₀ two_ne_zero]
    unfold ell at hy2
    linarith
  have : Int.log 2 y = Int.log 2 x := by omega
  simp [ell, this]

lemma ell_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : ell x ≤ ell y :=
  zpow_le_zpow_right₀ (by norm_num) (Int.log_mono_right hx hxy)

lemma two_mul_ell_le {x y : ℝ} (h : ell x < ell y) : 2 * ell x ≤ ell y := by
  unfold ell at *
  have hlt : Int.log 2 x < Int.log 2 y := (zpow_lt_zpow_iff_right₀ (by norm_num)).mp h
  have hle : Int.log 2 x + 1 ≤ Int.log 2 y := by omega
  have := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hle
  rw [zpow_add_one₀ two_ne_zero] at this
  linarith

lemma two_mul_ell_le_half {x : ℝ} (hx : 0 < x) (hx2 : x < 1 / 2) : 2 * ell x ≤ 1 / 2 := by
  have h1 : ell x < (2 : ℝ) ^ (-1 : ℤ) := by
    rw [zpow_neg_one]; linarith [ell_le hx]
  unfold ell at *
  have hlt : Int.log 2 x < -1 := (zpow_lt_zpow_iff_right₀ (by norm_num)).mp h1
  have hle : Int.log 2 x + 1 ≤ -1 := by omega
  have := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hle
  rw [zpow_add_one₀ two_ne_zero, zpow_neg_one] at this
  linarith

lemma ell_zpow (k : ℤ) : ell ((2 : ℝ) ^ k) = (2 : ℝ) ^ k := by
  have := Int.log_zpow (R := ℝ) (b := 2) (by norm_num) k
  simp only [Nat.cast_ofNat] at this
  simp [ell, this]

/- ## The fixed points `X m = 2^{-m-1}` -/

/-- The fixed points `X m = 2^{-m-1}` of `h`. -/
noncomputable def X (m : ℕ) : ℝ := (2 : ℝ) ^ (-(m : ℤ) - 1)

lemma X_pos (m : ℕ) : 0 < X m := zpow_pos (by norm_num) _

lemma X_succ (m : ℕ) : 2 * X (m + 1) = X m := by
  unfold X
  have : (-((m + 1 : ℕ) : ℤ) - 1) + 1 = -(m : ℤ) - 1 := by push_cast; ring
  rw [← this, zpow_add_one₀ two_ne_zero]
  ring

lemma X_succ_lt (m : ℕ) : X (m + 1) < X m := by
  have := X_succ m
  have := X_pos (m + 1)
  linarith

lemma X_zero : X 0 = 1 / 2 := by
  simp [X]

lemma X_le_half (m : ℕ) : X m ≤ 1 / 2 := by
  induction m with
  | zero => rw [X_zero]
  | succ n ih => linarith [X_succ_lt n]

lemma ell_X (m : ℕ) : ell (X m) = X m := ell_zpow _

/- ## Dyadic blocks near `1` -/

/-- `ellR x = 2 ^ (⌈log₂ (1 - x)⌉ - 1)`, so that `x ∈ [1 - 2 ellR x, 1 - ellR x)`. -/
noncomputable def ellR (x : ℝ) : ℝ := (2 : ℝ) ^ (Int.clog 2 (1 - x) - 1)

lemma ellR_pos (x : ℝ) : 0 < ellR x := zpow_pos (by norm_num) _

lemma two_mul_ellR (x : ℝ) : 2 * ellR x = (2 : ℝ) ^ (Int.clog 2 (1 - x)) := by
  unfold ellR
  rw [zpow_sub₀ two_ne_zero, zpow_one]
  ring

lemma one_sub_two_mul_ellR_le (x : ℝ) : 1 - 2 * ellR x ≤ x := by
  have := Int.self_le_zpow_clog (R := ℝ) (b := 2) (by norm_num) (1 - x)
  simp only [Nat.cast_ofNat] at this
  rw [two_mul_ellR]
  linarith

lemma lt_one_sub_ellR {x : ℝ} (hx : x < 1) : x < 1 - ellR x := by
  have := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) (show 0 < 1 - x by linarith)
  simp only [Nat.cast_ofNat] at this
  unfold ellR
  linarith

lemma ellR_eq_of_mem {x y : ℝ} (hy1 : 1 - 2 * ellR x ≤ y) (hy2 : y < 1 - ellR x) :
    ellR y = ellR x := by
  have hr : 0 < 1 - y := by linarith [ellR_pos x]
  have h1 : Int.clog 2 (1 - y) ≤ Int.clog 2 (1 - x) := by
    refine (Int.le_zpow_iff_clog_le (R := ℝ) (b := 2) (by norm_num) hr).mp ?_
    simp only [Nat.cast_ofNat]
    rw [← two_mul_ellR]
    linarith
  have h2 : Int.clog 2 (1 - x) - 1 < Int.clog 2 (1 - y) := by
    refine (Int.zpow_lt_iff_lt_clog (R := ℝ) (b := 2) (by norm_num) hr).mp ?_
    simp only [Nat.cast_ofNat]
    unfold ellR at hy2
    linarith
  have : Int.clog 2 (1 - y) = Int.clog 2 (1 - x) := by omega
  simp [ellR, this]

lemma ellR_anti {x y : ℝ} (hxy : x ≤ y) (hy : y < 1) : ellR y ≤ ellR x :=
  zpow_le_zpow_right₀ (by norm_num)
    (by have := Int.clog_mono_right (b := 2) (show 0 < 1 - y by linarith)
          (show 1 - y ≤ 1 - x by linarith); omega)

lemma two_mul_ellR_le {x y : ℝ} (h : ellR y < ellR x) : 2 * ellR y ≤ ellR x := by
  unfold ellR at *
  have hlt : Int.clog 2 (1 - y) - 1 < Int.clog 2 (1 - x) - 1 :=
    (zpow_lt_zpow_iff_right₀ (by norm_num)).mp h
  have hle : Int.clog 2 (1 - y) - 1 + 1 ≤ Int.clog 2 (1 - x) - 1 := by omega
  have := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hle
  rw [zpow_add_one₀ two_ne_zero] at this
  linarith

lemma half_le_one_sub_two_mul_ellR {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x < 1) :
    1 / 2 ≤ 1 - 2 * ellR x := by
  have hr : 0 < 1 - x := by linarith
  have h1 : Int.clog 2 (1 - x) ≤ -1 := by
    refine (Int.le_zpow_iff_clog_le (R := ℝ) (b := 2) (by norm_num) hr).mp ?_
    simp only [Nat.cast_ofNat, zpow_neg_one]
    linarith
  have := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) h1
  rw [zpow_neg_one] at this
  rw [two_mul_ellR]
  linarith

/-- The fixed points `Y m = 1 - 2^{-m-1}` near `1`. -/
noncomputable def Y (m : ℕ) : ℝ := 1 - X m

lemma ellR_Y (m : ℕ) : ellR (Y m) = X (m + 1) := by
  unfold ellR Y
  have h1 : 1 - (1 - X m) = X m := by ring
  rw [h1]
  have := Int.clog_zpow (R := ℝ) (b := 2) (by norm_num) (-(m : ℤ) - 1)
  simp only [Nat.cast_ofNat] at this
  unfold X
  rw [this]
  congr 1
  push_cast
  ring

lemma Y_succ_eq (m : ℕ) : Y (m + 1) = 1 - ellR (Y m) := by
  rw [ellR_Y]; rfl

lemma one_sub_two_ellR_Y (m : ℕ) : 1 - 2 * ellR (Y m) = Y m := by
  rw [ellR_Y, X_succ]; rfl

lemma Y_lt_one (m : ℕ) : Y m < 1 := by unfold Y; linarith [X_pos m]

lemma half_le_Y (m : ℕ) : 1 / 2 ≤ Y m := by unfold Y; linarith [X_le_half m]

lemma Y_lt_succ (m : ℕ) : Y m < Y (m + 1) := by unfold Y; linarith [X_succ_lt m]

lemma ell_lt_two_mul_ell (x : ℝ) : ell x < 2 * ell x := by linarith [ell_pos x]

lemma blockR_lt (x : ℝ) : 1 - 2 * ellR x < 1 - ellR x := by linarith [ellR_pos x]

lemma mem_blockR {x : ℝ} (hx1 : x < 1) : x ∈ Ico (1 - 2 * ellR x) (1 - ellR x) :=
  ⟨one_sub_two_mul_ellR_le x, lt_one_sub_ellR hx1⟩

lemma mem_block {x : ℝ} (hx0 : 0 < x) : x ∈ Ico (ell x) (2 * ell x) :=
  ⟨ell_le hx0, lt_two_mul_ell x⟩

lemma interval_pos_of_pos (f : Dlab.IntervalAut) {a : unitInterval} (ha : 0 < (a : ℝ)) :
    0 < ((f a : unitInterval) : ℝ) := by
  have h0 : f 0 = 0 := f.map_bot
  have : f 0 < f a := f.strictMono (show (0 : unitInterval) < a from ha)
  rw [h0] at this
  exact this

lemma interval_lt_one_of_lt (f : Dlab.IntervalAut) {a : unitInterval} (ha : (a : ℝ) < 1) :
    ((f a : unitInterval) : ℝ) < 1 := by
  have h1 : f 1 = 1 := f.map_top
  have : f a < f 1 := f.strictMono (show a < (1 : unitInterval) from ha)
  rw [h1] at this
  exact this

/- ## The functions `hF` and `hInvF` -/

section Conj

variable [S : SlopeChoice]

/-- The conjugating homeomorphism: a two-slope bump on every dyadic block inside `(0, 1/2)` and
on every dyadic block inside `[1/2, 1)`; the identity outside `(0, 1)`. -/
noncomputable def hF (x : ℝ) : ℝ :=
  if x ≤ 0 then x
  else if x < 1 / 2 then bumpF (ell x) (2 * ell x) x
  else if x < 1 then bumpF (1 - 2 * ellR x) (1 - ellR x) x
  else x

/-- The inverse of `hF`. -/
noncomputable def hInvF (y : ℝ) : ℝ :=
  if y ≤ 0 then y
  else if y < 1 / 2 then bumpInvF (ell y) (2 * ell y) y
  else if y < 1 then bumpInvF (1 - 2 * ellR y) (1 - ellR y) y
  else y

lemma hF_of_nonpos {x : ℝ} (hx : x ≤ 0) : hF x = x := by simp [hF, hx]

lemma hF_block {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    hF x = bumpF (ell x) (2 * ell x) x := by
  simp only [hF, not_le.mpr hx0, hx1, ↓reduceIte]

lemma hF_blockR {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x < 1) :
    hF x = bumpF (1 - 2 * ellR x) (1 - ellR x) x := by
  have h0 : ¬ x ≤ 0 := not_le.mpr (by linarith)
  simp only [hF, h0, not_lt.mpr hx0, hx1, ↓reduceIte]

lemma hF_of_one_le {x : ℝ} (hx : 1 ≤ x) : hF x = x := by
  have h0 : ¬ x ≤ 0 := not_le.mpr (by linarith)
  have h1 : ¬ x < 1 / 2 := not_lt.mpr (by linarith)
  simp only [hF, h0, h1, not_lt.mpr hx, ↓reduceIte]

lemma hInvF_of_nonpos {y : ℝ} (hy : y ≤ 0) : hInvF y = y := by simp [hInvF, hy]

lemma hInvF_block {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 2) :
    hInvF y = bumpInvF (ell y) (2 * ell y) y := by
  simp only [hInvF, not_le.mpr hy0, hy1, ↓reduceIte]

lemma hInvF_blockR {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) :
    hInvF y = bumpInvF (1 - 2 * ellR y) (1 - ellR y) y := by
  have h0 : ¬ y ≤ 0 := not_le.mpr (by linarith)
  simp only [hInvF, h0, not_lt.mpr hy0, hy1, ↓reduceIte]

lemma hInvF_of_one_le {y : ℝ} (hy : 1 ≤ y) : hInvF y = y := by
  have h0 : ¬ y ≤ 0 := not_le.mpr (by linarith)
  have h1 : ¬ y < 1 / 2 := not_lt.mpr (by linarith)
  simp only [hInvF, h0, h1, not_lt.mpr hy, ↓reduceIte]

/-- `hF` maps each dyadic block near `0` to itself. -/
lemma hF_mem_block {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    ell x ≤ hF x ∧ hF x < 2 * ell x := by
  rw [hF_block hx0 hx1]
  exact bumpF_mem_Ico (ell_lt_two_mul_ell x) (mem_block hx0)

lemma hInvF_mem_block {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 2) :
    ell y ≤ hInvF y ∧ hInvF y < 2 * ell y := by
  rw [hInvF_block hy0 hy1]
  exact bumpInvF_mem_Ico (ell_lt_two_mul_ell y) (mem_block hy0)

/-- `hF` maps each dyadic block near `1` to itself. -/
lemma hF_mem_blockR {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x < 1) :
    1 - 2 * ellR x ≤ hF x ∧ hF x < 1 - ellR x := by
  rw [hF_blockR hx0 hx1]
  exact bumpF_mem_Ico (blockR_lt x) (mem_blockR hx1)

lemma hInvF_mem_blockR {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) :
    1 - 2 * ellR y ≤ hInvF y ∧ hInvF y < 1 - ellR y := by
  rw [hInvF_blockR hy0 hy1]
  exact bumpInvF_mem_Ico (blockR_lt y) (mem_blockR hy1)

lemma hF_block_bounds {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) :
    0 < hF x ∧ hF x < 1 / 2 := by
  obtain ⟨h1, h2⟩ := hF_mem_block hx0 hx1
  exact ⟨lt_of_lt_of_le (ell_pos x) h1, lt_of_lt_of_le h2 (two_mul_ell_le_half hx0 hx1)⟩

lemma hInvF_block_bounds {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 2) :
    0 < hInvF y ∧ hInvF y < 1 / 2 := by
  obtain ⟨h1, h2⟩ := hInvF_mem_block hy0 hy1
  exact ⟨lt_of_lt_of_le (ell_pos y) h1, lt_of_lt_of_le h2 (two_mul_ell_le_half hy0 hy1)⟩

lemma hF_blockR_bounds {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x < 1) :
    1 / 2 ≤ hF x ∧ hF x < 1 := by
  obtain ⟨h1, h2⟩ := hF_mem_blockR hx0 hx1
  exact ⟨(half_le_one_sub_two_mul_ellR hx0 hx1).trans h1, by linarith [ellR_pos x]⟩

lemma hInvF_blockR_bounds {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) :
    1 / 2 ≤ hInvF y ∧ hInvF y < 1 := by
  obtain ⟨h1, h2⟩ := hInvF_mem_blockR hy0 hy1
  exact ⟨(half_le_one_sub_two_mul_ellR hy0 hy1).trans h1, by linarith [ellR_pos y]⟩

lemma ell_hF {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / 2) : ell (hF x) = ell x :=
  ell_eq_of_mem (hF_mem_block hx0 hx1).1 (hF_mem_block hx0 hx1).2

lemma ell_hInvF {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1 / 2) : ell (hInvF y) = ell y :=
  ell_eq_of_mem (hInvF_mem_block hy0 hy1).1 (hInvF_mem_block hy0 hy1).2

lemma ellR_hF {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x < 1) : ellR (hF x) = ellR x :=
  ellR_eq_of_mem (hF_mem_blockR hx0 hx1).1 (hF_mem_blockR hx0 hx1).2

lemma ellR_hInvF {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) : ellR (hInvF y) = ellR y :=
  ellR_eq_of_mem (hInvF_mem_blockR hy0 hy1).1 (hInvF_mem_blockR hy0 hy1).2

lemma hInvF_hF (x : ℝ) : hInvF (hF x) = x := by
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [hF_of_nonpos hx0, hInvF_of_nonpos hx0]
  rcases lt_or_ge x (1 / 2) with hx1 | hx1
  · obtain ⟨h0, h1⟩ := hF_block_bounds hx0 hx1
    rw [hInvF_block h0 h1, ell_hF hx0 hx1, hF_block hx0 hx1]
    exact bumpInvF_bumpF (ell_lt_two_mul_ell x) x
  rcases lt_or_ge x 1 with hx2 | hx2
  · obtain ⟨h0, h1⟩ := hF_blockR_bounds hx1 hx2
    rw [hInvF_blockR h0 h1, ellR_hF hx1 hx2, hF_blockR hx1 hx2]
    exact bumpInvF_bumpF (blockR_lt x) x
  · rw [hF_of_one_le hx2, hInvF_of_one_le hx2]

lemma hF_hInvF (y : ℝ) : hF (hInvF y) = y := by
  rcases le_or_gt y 0 with hy0 | hy0
  · rw [hInvF_of_nonpos hy0, hF_of_nonpos hy0]
  rcases lt_or_ge y (1 / 2) with hy1 | hy1
  · obtain ⟨h0, h1⟩ := hInvF_block_bounds hy0 hy1
    rw [hF_block h0 h1, ell_hInvF hy0 hy1, hInvF_block hy0 hy1]
    exact bumpF_bumpInvF (ell_lt_two_mul_ell y) y
  rcases lt_or_ge y 1 with hy2 | hy2
  · obtain ⟨h0, h1⟩ := hInvF_blockR_bounds hy1 hy2
    rw [hF_blockR h0 h1, ellR_hInvF hy1 hy2, hInvF_blockR hy1 hy2]
    exact bumpF_bumpInvF (blockR_lt y) y
  · rw [hInvF_of_one_le hy2, hF_of_one_le hy2]

lemma hF_strictMono : StrictMono hF := by
  intro x y hxy
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [hF_of_nonpos hx0]
    rcases le_or_gt y 0 with hy0 | hy0
    · rwa [hF_of_nonpos hy0]
    rcases lt_or_ge y (1 / 2) with hy1 | hy1
    · linarith [(hF_block_bounds hy0 hy1).1]
    rcases lt_or_ge y 1 with hy2 | hy2
    · linarith [(hF_blockR_bounds hy1 hy2).1]
    · rw [hF_of_one_le hy2]; linarith
  rcases lt_or_ge x (1 / 2) with hx1 | hx1
  · have hbx := hF_block_bounds hx0 hx1
    rcases lt_or_ge y (1 / 2) with hy1 | hy1
    · have hy0 : 0 < y := by linarith
      rcases (ell_mono hx0 hxy.le).lt_or_eq with hell | hell
      · have h1 := (hF_mem_block hx0 hx1).2
        have h2 := (hF_mem_block hy0 hy1).1
        have h3 := two_mul_ell_le hell
        linarith
      · rw [hF_block hx0 hx1, hF_block hy0 hy1, ← hell]
        exact bumpF_strictMono (ell_lt_two_mul_ell x) hxy
    rcases lt_or_ge y 1 with hy2 | hy2
    · linarith [(hF_blockR_bounds hy1 hy2).1]
    · rw [hF_of_one_le hy2]; linarith
  rcases lt_or_ge x 1 with hx2 | hx2
  · have hbx := hF_blockR_bounds hx1 hx2
    rcases lt_or_ge y 1 with hy2 | hy2
    · have hy1 : 1 / 2 ≤ y := by linarith
      rcases (ellR_anti hxy.le hy2).lt_or_eq with hell | hell
      · have h1 := (hF_mem_blockR hx1 hx2).2
        have h2 := (hF_mem_blockR hy1 hy2).1
        have h3 := two_mul_ellR_le hell
        linarith
      · rw [hF_blockR hx1 hx2, hF_blockR hy1 hy2, hell]
        exact bumpF_strictMono (blockR_lt x) hxy
    · rw [hF_of_one_le hy2]; linarith
  · rw [hF_of_one_le hx2, hF_of_one_le (by linarith)]
    exact hxy

lemma le_hF (x : ℝ) : x ≤ hF x := by
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [hF_of_nonpos hx0]
  rcases lt_or_ge x (1 / 2) with hx1 | hx1
  · rw [hF_block hx0 hx1]; exact le_bumpF (ell_lt_two_mul_ell x) x
  rcases lt_or_ge x 1 with hx2 | hx2
  · rw [hF_blockR hx1 hx2]; exact le_bumpF (blockR_lt x) x
  · rw [hF_of_one_le hx2]

lemma hF_le_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1 / 2) : hF x ≤ 2 * x := by
  rcases hx0.lt_or_eq with hx0 | rfl
  · have h1 := (hF_mem_block hx0 hx1).2
    have h2 := ell_le hx0
    linarith
  · rw [hF_of_nonpos le_rfl]; norm_num

lemma hInvF_le_self {y : ℝ} (hy0 : 0 ≤ y) : hInvF y ≤ y := by
  rcases hy0.lt_or_eq with hy0 | rfl
  · rcases lt_or_ge y (1 / 2) with hy1 | hy1
    · rw [hInvF_block hy0 hy1]
      exact bumpInvF_le (ell_lt_two_mul_ell y) y
    rcases lt_or_ge y 1 with hy2 | hy2
    · rw [hInvF_blockR hy1 hy2]
      exact bumpInvF_le (blockR_lt y) y
    · rw [hInvF_of_one_le hy2]
  · rw [hInvF_of_nonpos le_rfl]

lemma two_mul_sub_one_le_hInvF {y : ℝ} (hy0 : 1 / 2 ≤ y) (hy1 : y < 1) : 2 * y - 1 ≤ hInvF y := by
  have h1 := (hInvF_mem_blockR hy0 hy1).1
  have h2 := lt_one_sub_ellR hy1
  linarith

lemma hF_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : hF x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases hx0.lt_or_eq with hx0 | rfl
  · rcases lt_or_ge x (1 / 2) with hx2 | hx2
    · obtain ⟨h0, h1⟩ := hF_block_bounds hx0 hx2
      exact ⟨h0.le, by linarith⟩
    rcases hx1.lt_or_eq with hx3 | rfl
    · obtain ⟨h0, h1⟩ := hF_blockR_bounds hx2 hx3
      exact ⟨by linarith, h1.le⟩
    · rw [hF_of_one_le le_rfl]; exact ⟨zero_le_one, le_rfl⟩
  · rw [hF_of_nonpos le_rfl]; exact ⟨le_rfl, zero_le_one⟩

lemma hInvF_mem_Icc {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : hInvF y ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hy0, hy1⟩ := hy
  rcases hy0.lt_or_eq with hy0 | rfl
  · rcases lt_or_ge y (1 / 2) with hy2 | hy2
    · obtain ⟨h0, h1⟩ := hInvF_block_bounds hy0 hy2
      exact ⟨h0.le, by linarith⟩
    rcases hy1.lt_or_eq with hy3 | rfl
    · obtain ⟨h0, h1⟩ := hInvF_blockR_bounds hy2 hy3
      exact ⟨by linarith, h1.le⟩
    · rw [hInvF_of_one_le le_rfl]; exact ⟨zero_le_one, le_rfl⟩
  · rw [hInvF_of_nonpos le_rfl]; exact ⟨le_rfl, zero_le_one⟩

lemma hF_realRLin {a : ℝ} (ha0 : 0 < a) : RealRLin hF a := by
  rcases lt_or_ge a (1 / 2) with ha1 | ha1
  · obtain ⟨ε, hε, s, hs, hh⟩ := bumpF_realRLin (ell_lt_two_mul_ell a) a
    have hgap : 0 < 2 * ell a - a := by linarith [lt_two_mul_ell a]
    refine realRLin_of_eq (ε := min ε (2 * ell a - a)) (lt_min hε hgap) s hs fun x hx1 hx2 ↦ ?_
    have hx2' : x < 2 * ell a := by linarith [min_le_right ε (2 * ell a - a)]
    have hxhalf : x < 1 / 2 := lt_of_lt_of_le hx2' (two_mul_ell_le_half ha0 ha1)
    have hx0 : 0 < x := by linarith
    have hellx : ell x = ell a := ell_eq_of_mem (by linarith [ell_le ha0]) hx2'
    rw [hF_block hx0 hxhalf, hF_block ha0 ha1, hellx]
    exact hh x hx1 (by linarith [min_le_left ε (2 * ell a - a)])
  rcases lt_or_ge a 1 with ha2 | ha2
  · obtain ⟨ε, hε, s, hs, hh⟩ := bumpF_realRLin (blockR_lt a) a
    have hgap : 0 < 1 - ellR a - a := by linarith [lt_one_sub_ellR ha2]
    refine realRLin_of_eq (ε := min ε (1 - ellR a - a)) (lt_min hε hgap) s hs fun x hx1 hx2 ↦ ?_
    have hx2' : x < 1 - ellR a := by linarith [min_le_right ε (1 - ellR a - a)]
    have hx1' : x < 1 := by linarith [ellR_pos a]
    have hellx : ellR x = ellR a :=
      ellR_eq_of_mem (by linarith [one_sub_two_mul_ellR_le a]) hx2'
    rw [hF_blockR (by linarith) hx1', hF_blockR ha1 ha2, hellx]
    exact hh x hx1 (by linarith [min_le_left ε (1 - ellR a - a)])
  · refine realRLin_of_eq (ε := 1) one_pos 1 S.K.one_mem fun x hx1 _ ↦ ?_
    rw [hF_of_one_le (by linarith), hF_of_one_le ha2, slope_one]
    ring

lemma hInvF_realRLin {a : ℝ} (ha0 : 0 < a) : RealRLin hInvF a := by
  rcases lt_or_ge a (1 / 2) with ha1 | ha1
  · obtain ⟨ε, hε, s, hs, hh⟩ := bumpInvF_realRLin (ell_lt_two_mul_ell a) a
    have hgap : 0 < 2 * ell a - a := by linarith [lt_two_mul_ell a]
    refine realRLin_of_eq (ε := min ε (2 * ell a - a)) (lt_min hε hgap) s hs fun x hx1 hx2 ↦ ?_
    have hx2' : x < 2 * ell a := by linarith [min_le_right ε (2 * ell a - a)]
    have hxhalf : x < 1 / 2 := lt_of_lt_of_le hx2' (two_mul_ell_le_half ha0 ha1)
    have hx0 : 0 < x := by linarith
    have hellx : ell x = ell a := ell_eq_of_mem (by linarith [ell_le ha0]) hx2'
    rw [hInvF_block hx0 hxhalf, hInvF_block ha0 ha1, hellx]
    exact hh x hx1 (by linarith [min_le_left ε (2 * ell a - a)])
  rcases lt_or_ge a 1 with ha2 | ha2
  · obtain ⟨ε, hε, s, hs, hh⟩ := bumpInvF_realRLin (blockR_lt a) a
    have hgap : 0 < 1 - ellR a - a := by linarith [lt_one_sub_ellR ha2]
    refine realRLin_of_eq (ε := min ε (1 - ellR a - a)) (lt_min hε hgap) s hs fun x hx1 hx2 ↦ ?_
    have hx2' : x < 1 - ellR a := by linarith [min_le_right ε (1 - ellR a - a)]
    have hx1' : x < 1 := by linarith [ellR_pos a]
    have hellx : ellR x = ellR a :=
      ellR_eq_of_mem (by linarith [one_sub_two_mul_ellR_le a]) hx2'
    rw [hInvF_blockR (by linarith) hx1', hInvF_blockR ha1 ha2, hellx]
    exact hh x hx1 (by linarith [min_le_left ε (1 - ellR a - a)])
  · refine realRLin_of_eq (ε := 1) one_pos 1 S.K.one_mem fun x hx1 _ ↦ ?_
    rw [hInvF_of_one_le (by linarith), hInvF_of_one_le ha2, slope_one]
    ring

/-- `h` fixes the points `Y m` near `1`. -/
lemma hF_Y (m : ℕ) : hF (Y m) = Y m := by
  rw [hF_blockR (half_le_Y m) (Y_lt_one m), one_sub_two_ellR_Y]
  exact bumpF_of_le le_rfl

/-- `h` moves every point strictly between `Y m` and `Y (m+1)` to the right. -/
lemma lt_hF_R {m : ℕ} {y : ℝ} (hy1 : Y m < y) (hy2 : y < Y (m + 1)) : y < hF y := by
  have hy0 : 1 / 2 ≤ y := by linarith [half_le_Y m]
  have hyl : y < 1 := by linarith [Y_lt_one (m + 1)]
  have hell : ellR y = ellR (Y m) := by
    refine ellR_eq_of_mem (by rw [one_sub_two_ellR_Y]; exact hy1.le) ?_
    rw [← Y_succ_eq]; exact hy2
  rw [hF_blockR hy0 hyl, hell, one_sub_two_ellR_Y, ← Y_succ_eq]
  exact lt_bumpF hy1 hy2

/-- `h` fixes the points `X m`. -/
lemma hF_X (m : ℕ) : hF (X m) = X m := by
  rcases (X_le_half m).lt_or_eq with h | h
  · rw [hF_block (X_pos m) h, ell_X]
    exact bumpF_of_le le_rfl
  · have hY : Y 0 = X m := by
      unfold Y; rw [X_zero, h]; norm_num
    rw [← hY]
    exact hF_Y 0

/-- `h` moves every point strictly between `X (m+1)` and `X m` to the right. -/
lemma lt_hF {m : ℕ} {y : ℝ} (hy1 : X (m + 1) < y) (hy2 : y < X m) : y < hF y := by
  have hy0 : 0 < y := (X_pos (m + 1)).trans hy1
  have hyhalf : y < 1 / 2 := lt_of_lt_of_le hy2 (X_le_half m)
  have hell : ell y = X (m + 1) := by
    rw [← ell_X (m + 1)]
    refine ell_eq_of_mem (by rw [ell_X]; exact hy1.le) ?_
    rw [ell_X, X_succ]; exact hy2
  rw [hF_block hy0 hyhalf, hell, X_succ]
  exact lt_bumpF hy1 hy2

/- ## The interval automorphism `hAut` and the automorphism `α` -/

/-- The conjugating homeomorphism as an order automorphism of `[0, 1]`. -/
noncomputable def hAut : Dlab.IntervalAut :=
  mkIntervalAut hF hInvF (fun _ hx ↦ hF_mem_Icc hx) (fun _ hy ↦ hInvF_mem_Icc hy)
    (fun x _ ↦ hInvF_hF x) (fun y _ ↦ hF_hInvF y) (hF_strictMono.strictMonoOn _)

lemma hAut_apply (x : unitInterval) : (hAut x : ℝ) = hF x := rfl

lemma hAut_inv_apply (y : unitInterval) : (hAut⁻¹ y : ℝ) = hInvF y := rfl

lemma extHom_hAut (x : ℝ) : extHom hAut x = hF x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have := extHom_apply_coe hAut ⟨x, hx⟩
    rw [this, hAut_apply]
  · rw [extHom_apply_of_not_mem _ hx]
    rcases not_and_or.mp hx with hx0 | hx1
    · exact (hF_of_nonpos (by linarith [not_le.mp hx0])).symm
    · exact (hF_of_one_le (by linarith [not_le.mp hx1])).symm

lemma hAut_zero : hAut 0 = 0 := hAut.map_bot

lemma hAut_one : hAut 1 = 1 := hAut.map_top

lemma rlin_hAut {a : unitInterval} (ha : 0 < (a : ℝ)) : RLin S.K hAut a :=
  RLin.of_real le_rfl hAut_apply (hF_realRLin ha)

lemma rlin_hAut_inv {a : unitInterval} (ha : 0 < (a : ℝ)) : RLin S.K hAut⁻¹ a :=
  RLin.of_real le_rfl hAut_inv_apply (hInvF_realRLin ha)

/-- Conjugation by `hAut` preserves `D_K([0,1])`. -/
lemma conj_isElement {f : Dlab.IntervalAut} (hf : Dlab.IsElement S.K f) :
    Dlab.IsElement S.K (hAut⁻¹ * f * hAut) := by
  obtain ⟨hlin, h0, h1⟩ := hf
  obtain ⟨δ, hδ, hδf⟩ := exists_id_near_zero h0
  obtain ⟨δ', hδ', hδ'f⟩ := exists_id_near_one h1
  have hid0 : ∀ x : unitInterval, (x : ℝ) < min (δ / 2) (1 / 4) →
      (hAut⁻¹ * f * hAut) x = x := by
    intro x hx
    have hxδ : (x : ℝ) < δ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx4 : (x : ℝ) < 1 / 4 := lt_of_lt_of_le hx (min_le_right _ _)
    have hhx : ((hAut x : unitInterval) : ℝ) < δ := by
      rw [hAut_apply]
      have := hF_le_two_mul x.2.1 (by linarith)
      linarith
    have hfx : f (hAut x) = hAut x := hδf _ hhx
    show hAut⁻¹ (f (hAut x)) = x
    rw [hfx]
    exact hAut.symm_apply_apply x
  refine ⟨fun a ha ↦ ?_, isIdentityNearZero_of (lt_min (by linarith) (by norm_num)) hid0,
    isIdentityNearOne_of (δ := max δ' (1 / 2)) (max_lt hδ' (by norm_num)) fun x hx ↦ ?_⟩
  · by_cases ha0 : (a : ℝ) = 0
    · have : a = 0 := Subtype.ext ha0
      rw [this]
      exact RLin.zero_of_id (lt_min (by linarith) (by norm_num)) hid0
    have ha0' : 0 < (a : ℝ) := lt_of_le_of_ne a.2.1 (Ne.symm ha0)
    have ha1 : (a : ℝ) < 1 := ha
    have hr1 := rlin_hAut ha0'
    have hr2 : RLin S.K f (hAut a) := hlin (hAut a) (interval_lt_one_of_lt hAut ha1)
    have hr3 : RLin S.K hAut⁻¹ (f (hAut a)) :=
      rlin_hAut_inv (interval_pos_of_pos f (interval_pos_of_pos hAut ha0'))
    rw [mul_assoc]
    exact RLin.mul (RLin.mul hr1 hr2) hr3
  · have hxδ' : δ' < (x : ℝ) := lt_of_le_of_lt (le_max_left _ _) hx
    have hhx : δ' < ((hAut x : unitInterval) : ℝ) := by
      rw [hAut_apply]; exact lt_of_lt_of_le hxδ' (le_hF x)
    show hAut⁻¹ (f (hAut x)) = x
    rw [hδ'f _ hhx]
    exact hAut.symm_apply_apply x

/-- Conjugation by `hAut⁻¹` preserves `D_K([0,1])`. -/
lemma conj_inv_isElement {f : Dlab.IntervalAut} (hf : Dlab.IsElement S.K f) :
    Dlab.IsElement S.K (hAut * f * hAut⁻¹) := by
  obtain ⟨hlin, h0, h1⟩ := hf
  obtain ⟨δ, hδ, hδf⟩ := exists_id_near_zero h0
  obtain ⟨δ', hδ', hδ'f⟩ := exists_id_near_one h1
  have hid0 : ∀ x : unitInterval, (x : ℝ) < δ → (hAut * f * hAut⁻¹) x = x := by
    intro x hx
    have hhx : ((hAut⁻¹ x : unitInterval) : ℝ) < δ := by
      rw [hAut_inv_apply]
      exact lt_of_le_of_lt (hInvF_le_self x.2.1) hx
    have hfx : f (hAut⁻¹ x) = hAut⁻¹ x := hδf _ hhx
    show hAut (f (hAut⁻¹ x)) = x
    rw [hfx]
    exact hAut.apply_symm_apply x
  refine ⟨fun a ha ↦ ?_, isIdentityNearZero_of hδ hid0,
    isIdentityNearOne_of (δ := max ((1 + δ') / 2) (1 / 2)) (max_lt (by linarith) (by norm_num))
      fun x hx ↦ ?_⟩
  · by_cases ha0 : (a : ℝ) = 0
    · have : a = 0 := Subtype.ext ha0
      rw [this]
      exact RLin.zero_of_id hδ hid0
    have ha0' : 0 < (a : ℝ) := lt_of_le_of_ne a.2.1 (Ne.symm ha0)
    have ha1 : (a : ℝ) < 1 := ha
    have hr1 := rlin_hAut_inv ha0'
    have hr2 : RLin S.K f (hAut⁻¹ a) := hlin (hAut⁻¹ a) (interval_lt_one_of_lt hAut⁻¹ ha1)
    have hr3 : RLin S.K hAut (f (hAut⁻¹ a)) :=
      rlin_hAut (interval_pos_of_pos f (interval_pos_of_pos hAut⁻¹ ha0'))
    rw [mul_assoc]
    exact RLin.mul (RLin.mul hr1 hr2) hr3
  · have hx1 : (1 + δ') / 2 < (x : ℝ) := lt_of_le_of_lt (le_max_left _ _) hx
    have hxh : 1 / 2 ≤ (x : ℝ) := (le_max_right _ _).trans hx.le
    have hhx : δ' < ((hAut⁻¹ x : unitInterval) : ℝ) := by
      rw [hAut_inv_apply]
      rcases lt_or_ge (x : ℝ) 1 with hxl | hxl
      · have := two_mul_sub_one_le_hInvF hxh hxl; linarith
      · rw [hInvF_of_one_le hxl]; linarith
    show hAut (f (hAut⁻¹ x)) = x
    rw [hδ'f _ hhx]
    exact hAut.apply_symm_apply x

/-- The automorphism `α f = h⁻¹ f h` of `D_K([0,1])`. -/
noncomputable def α : DlabGroup S.K ≃* DlabGroup S.K where
  toFun f := ⟨hAut⁻¹ * f.1 * hAut, conj_isElement f.2⟩
  invFun f := ⟨hAut * f.1 * hAut⁻¹, conj_inv_isElement f.2⟩
  left_inv f := Subtype.ext (by simp only; group)
  right_inv f := Subtype.ext (by simp only; group)
  map_mul' f g := Subtype.ext (by
    change hAut⁻¹ * (f.1 * g.1) * hAut = (hAut⁻¹ * f.1 * hAut) * (hAut⁻¹ * g.1 * hAut)
    group)

lemma α_val (f : DlabGroup S.K) : (α f).1 = hAut⁻¹ * f.1 * hAut := rfl

end Conj

end Kourovka21149

end

/- ## Section: `Source` -/

section

/-
# The source datum for `D_K([0,1])`

We package Dlab's group `D_K([0,1])` (for a slope choice `S` with `K = S.K`), its standard action
on `ℝ`, the automorphism `α` and the bumps into a `SourceData`.
-/

open Set
open scoped unitInterval

namespace Kourovka21149

open LineAut

/-- The standard action of a Dlab group `D_K([0,1])` on `ℝ` (extended by the identity). -/
noncomputable def ι {K : Subgroup NNRealˣ} : DlabGroup K →* LineAut :=
  extHom.comp (Dlab.subgroup K).subtype

lemma ι_apply {K : Subgroup NNRealˣ} (f : DlabGroup K) : ι f = extHom f.1 := rfl

lemma ι_injective {K : Subgroup NNRealˣ} : Function.Injective (ι (K := K)) :=
  extHom_injective.comp Subtype.val_injective

lemma ι_dlab {K : Subgroup NNRealˣ} (f : DlabGroup K) : IsDlabLike (ι f) :=
  isDlabLike_extHom f.2.1

section Source

variable [S : SlopeChoice]

lemma ι_α (f : DlabGroup S.K) : ι (α f) = (extHom hAut)⁻¹ * ι f * extHom hAut := by
  rw [ι_apply, α_val, map_mul, map_mul, map_inv, ι_apply]

/-- A bump as an element of `D_K([0,1])`. -/
noncomputable def bumpElt {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) : DlabGroup S.K :=
  ⟨bumpAut hp hpq hq, bumpAut_isElement hp hpq hq⟩

lemma ι_bumpElt {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) (x : ℝ) :
    ι (bumpElt hp hpq hq) x = bumpF p q x :=
  extHom_bumpAut hp hpq hq x

lemma ι_bumpElt_moves {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    ι (bumpElt hp hpq hq) ((p + q) / 2) ≠ (p + q) / 2 := by
  rw [ι_bumpElt]
  exact (lt_bumpF (by linarith) (by linarith)).ne'

lemma bumpElt_ne_one {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    bumpElt hp hpq hq ≠ 1 := by
  intro h
  apply ι_bumpElt_moves hp hpq hq
  rw [h, map_one]
  rfl

/-- Two noncommuting bumps inside `(β, γ)`. -/
lemma exists_noncomm (β γ : ℝ) (hβ : 0 < β) (hβγ : β < γ) (hγ : γ < 1) :
    ∃ a b : DlabGroup S.K, ∃ p q : ℝ, β < p ∧ q < γ ∧
      (∀ x, x < p → ι a x = x ∧ ι b x = x) ∧ (∀ x, q < x → ι a x = x ∧ ι b x = x) ∧
      a * b ≠ b * a := by
  set L := γ - β with hL
  have hLpos : 0 < L := by linarith
  have hpa : 0 < β + L / 5 := by linarith
  have hpqa : β + L / 5 < β + 3 * L / 5 := by linarith
  have hqa : β + 3 * L / 5 < 1 := by linarith
  have hpb : 0 < β + 2 * L / 5 := by linarith
  have hpqb : β + 2 * L / 5 < β + 4 * L / 5 := by linarith
  have hqb : β + 4 * L / 5 < 1 := by linarith
  refine ⟨bumpElt hpa hpqa hqa, bumpElt hpb hpqb hqb, β + L / 5, β + 4 * L / 5, by linarith,
    by linarith, fun x hx ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [ι_bumpElt, ι_bumpElt]
    exact ⟨bumpF_of_le hx.le, bumpF_of_le (by linarith)⟩
  · rw [ι_bumpElt, ι_bumpElt]
    exact ⟨bumpF_of_ge hpqa (by linarith), bumpF_of_ge hpqb (by linarith)⟩
  · -- the second bump fixes `β + 2L/5`, the first one moves it into the support of the second
    intro hab
    have h := congrArg (fun g ↦ ι g (β + 2 * L / 5)) hab
    simp only [map_mul, mul_apply', ι_bumpElt] at h
    rw [bumpF_of_le (p := β + 2 * L / 5) le_rfl] at h
    have hy1 : β + 2 * L / 5 < bumpF (β + L / 5) (β + 3 * L / 5) (β + 2 * L / 5) :=
      lt_bumpF (by linarith) (by linarith)
    have hy2 : bumpF (β + L / 5) (β + 3 * L / 5) (β + 2 * L / 5) < β + 3 * L / 5 :=
      (bumpF_mem_Ico hpqa ⟨by linarith, by linarith⟩).2
    have := lt_bumpF (p := β + 2 * L / 5) (q := β + 4 * L / 5) hy1 (by linarith)
    linarith

/-- The source datum for `D_K([0,1])`. -/
noncomputable def source : SourceData (DlabGroup S.K) where
  ι := ι
  ι_injective := ι_injective
  ι_dlab := ι_dlab
  α := α
  c := extHom hAut
  α_spec := ι_α
  X := X
  X_pos := X_pos
  X_succ_lt := X_succ_lt
  c_fix m := by rw [extHom_hAut, hF_X]
  c_moves m y h1 h2 := by rw [extHom_hAut]; exact lt_hF h1 h2
  supply_small τ hτ := by
    set q := min τ (1 / 2) / 2 with hqdef
    have hmin : 0 < min τ (1 / 2) := lt_min hτ (by norm_num)
    have hq0 : 0 < q := by positivity
    have hp : 0 < q / 2 := by positivity
    have hpq : q / 2 < q := by linarith
    have hq1 : q < 1 := by linarith [min_le_right τ (1 / 2)]
    refine ⟨bumpElt hp hpq hq1, bumpElt_ne_one hp hpq hq1, ?_⟩
    have := fm_le_of_moved (ι_dlab _).idNearBot (ι_bumpElt_moves hp hpq hq1)
    have hqτ : q < τ := by linarith [min_le_left τ (1 / 2)]
    linarith
  supply_top := by
    have hp : (0 : ℝ) < 5 / 8 := by norm_num
    have hpq : (5 : ℝ) / 8 < 7 / 8 := by norm_num
    have hq : (7 : ℝ) / 8 < 1 := by norm_num
    refine ⟨bumpElt hp hpq hq, bumpElt_ne_one hp hpq hq, ?_⟩
    have := le_fm_of_forall (show ι (bumpElt hp hpq hq) ≠ 1 from fun h ↦
      bumpElt_ne_one hp hpq hq (ι_injective (by rw [h, map_one])))
      (p := 5 / 8) fun x hx ↦ by rw [ι_bumpElt]; exact bumpF_of_le hx.le
    rw [X_zero]
    linarith
  supply_comm β γ hβ hβγ hγ := by
    have : γ < 1 := by
      have := X_zero ▸ hγ
      linarith
    exact exists_noncomm β γ hβ hβγ this

end Source

end Kourovka21149

end

/- ## Section: `Order` -/

section

/-
# The Dlab order on `D_K([0,1])`

We equip `DlabGroup K = D_K([0,1])` with Dlab's first-disagreement order: `f < g` iff at the
first point where `f` and `g` differ, `f` lies below `g`. We show that it is a bi-invariant linear
order, that it agrees with the first-disagreement relation on `[0, 1]` (`IntervalFDLt`), and that
`α` is an order automorphism.

We then derive the key property of `Kourovka21149.Core` for every order-preserving or
order-reversing embedding.
-/

open Set
open scoped unitInterval

namespace Kourovka21149

open LineAut

/-- Dlab's strict order on `D_K([0,1])`. -/
def DlabLt {K : Subgroup NNRealˣ} (f g : DlabGroup K) : Prop := FDLt (ι f) (ι g)

lemma dlabLt_trichotomy {K : Subgroup NNRealˣ} (f g : DlabGroup K) : f = g ∨ DlabLt f g ∨ DlabLt g f := by
  have h : IsDlabLike ((ι f)⁻¹ * ι g) := by
    rw [← map_inv, ← map_mul]; exact ι_dlab _
  rcases fdlt_trichotomy h with h1 | h1 | h1
  · exact Or.inl (ι_injective h1)
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

/-- Dlab's linear order on `D_K([0,1])`. -/
noncomputable instance {K : Subgroup NNRealˣ} : LinearOrder (DlabGroup K) := by
  have : Std.Trichotomous (r := (@DlabLt K)) :=
    ⟨fun a b h₁ h₂ ↦ by
      rcases dlabLt_trichotomy a b with h | h | h
      · exact h
      · exact absurd h h₁
      · exact absurd h h₂⟩
  have : Std.Irrefl (α := DlabGroup K) (@DlabLt K) := ⟨fun a ↦ fdlt_irrefl _⟩
  have : IsTrans (DlabGroup K) (@DlabLt K) := ⟨fun _ _ _ h₁ h₂ ↦ fdlt_trans h₁ h₂⟩
  have : DecidableRel (α := DlabGroup K) (@DlabLt K) := Classical.decRel _
  have : IsStrictTotalOrder (DlabGroup K) (@DlabLt K) := {}
  exact linearOrderOfSTO (@DlabLt K)

lemma lt_iff_dlabLt {K : Subgroup NNRealˣ} (f g : DlabGroup K) : f < g ↔ DlabLt f g := Iff.rfl

lemma le_iff_eq_or_dlabLt {K : Subgroup NNRealˣ} (f g : DlabGroup K) : f ≤ g ↔ f = g ∨ DlabLt f g := Iff.rfl

/-- The order is Dlab's first-disagreement order on `[0, 1]`. -/
lemma lt_iff_intervalFDLt {K : Subgroup NNRealˣ} (f g : DlabGroup K) : f < g ↔ IntervalFDLt f.1 g.1 :=
  (intervalFDLt_iff f.1 g.1).symm

/-- The order is left invariant. -/
lemma mul_lt_mul_left' {K : Subgroup NNRealˣ} {f g : DlabGroup K} (h : f < g) (c : DlabGroup K) : c * f < c * g := by
  change FDLt (ι (c * f)) (ι (c * g))
  rw [map_mul, map_mul]
  exact fdlt_mul_left _ h

/-- The order is right invariant. -/
lemma mul_lt_mul_right' {K : Subgroup NNRealˣ} {f g : DlabGroup K} (h : f < g) (c : DlabGroup K) : f * c < g * c := by
  change FDLt (ι (f * c)) (ι (g * c))
  rw [map_mul, map_mul]
  exact fdlt_mul_right _ h

/-- The order is bi-invariant. -/
theorem dlabOrder_biInvariant {K : Subgroup NNRealˣ} (a b c : DlabGroup K) (h : a ≤ b) : c * a ≤ c * b ∧ a * c ≤ b * c := by
  rcases h.lt_or_eq with h | rfl
  · exact ⟨(mul_lt_mul_left' h c).le, (mul_lt_mul_right' h c).le⟩
  · exact ⟨le_rfl, le_rfl⟩

section OrderAut

variable [S : SlopeChoice]

lemma α_lt_iff (f g : DlabGroup S.K) : α f < α g ↔ f < g := by
  change FDLt (ι (α f)) (ι (α g)) ↔ FDLt (ι f) (ι g)
  rw [ι_α, ι_α, fdlt_conj_iff]

/-- `α` is an order automorphism of `D_K([0,1])`. -/
noncomputable def αo : DlabGroup S.K ≃*o DlabGroup S.K where
  toMulEquiv := α
  map_le_map_iff' := by
    intro f g
    change α f ≤ α g ↔ f ≤ g
    rw [le_iff_eq_or_dlabLt, le_iff_eq_or_dlabLt, α.injective.eq_iff]
    exact or_congr Iff.rfl (α_lt_iff f g)

@[simp] lemma αo_apply (f : DlabGroup S.K) : αo f = α f := rfl

/- ## The key property from order preservation -/

lemma exists_pos_version {g : DlabGroup S.K} (hg : g ≠ 1) :
    ∃ g' : DlabGroup S.K, 1 < g' ∧ (g' = g ∨ g' = g⁻¹) := by
  rcases lt_or_gt_of_ne hg with h | h
  · refine ⟨g⁻¹, ?_, Or.inr rfl⟩
    change FDLt (ι 1) (ι g⁻¹)
    rw [map_one, map_inv, one_fdlt_inv_iff]
    have : FDLt (ι g) (ι 1) := h
    rwa [map_one] at this
  · exact ⟨g, h, Or.inl rfl⟩

lemma fm_ι_of_version {g g' : DlabGroup S.K} (h : g' = g ∨ g' = g⁻¹) : fm (ι g') = fm (ι g) := by
  rcases h with rfl | rfl
  · rfl
  · rw [map_inv, fm_inv]

lemma one_fdlt_ι {g : DlabGroup S.K} (h : 1 < g) : FDLt 1 (ι g) := by
  have : FDLt (ι 1) (ι g) := h
  rwa [map_one] at this

/-- **Key property.** If `e` is an order-preserving or order-reversing embedding into Dlab-like
homeomorphisms, then `e` satisfies `source.KeyProp`. -/
theorem keyProp_of_mono (e : DlabGroup S.K →* LineAut) (he_dlab : ∀ g, IsDlabLike (e g))
    (hmono : (∀ f g : DlabGroup S.K, f < g → FDLt (e f) (e g)) ∨
      (∀ f g : DlabGroup S.K, f < g → FDLt (e g) (e f))) :
    source.KeyProp e := by
  intro s g₀ g hg₀ hfix hlt
  by_cases hg : g = 1
  · rw [hg, map_one]; exact (fixLeft s).one_mem
  obtain ⟨g₀', hpos₀, hv₀⟩ := exists_pos_version hg₀
  obtain ⟨g', hpos, hv⟩ := exists_pos_version hg
  have hfix₀ : e g₀' ∈ fixLeft s := by
    rcases hv₀ with rfl | rfl
    · exact hfix
    · rw [map_inv]; exact (fixLeft s).inv_mem hfix
  have hback : e g' ∈ fixLeft s → e g ∈ fixLeft s := by
    intro h
    rcases hv with rfl | rfl
    · exact h
    · have := (fixLeft s).inv_mem h
      rwa [map_inv, inv_inv] at this
  have hne₀ : ι g₀' ≠ 1 := by
    intro h
    have : g₀' = 1 := ι_injective (by rw [h, map_one])
    rw [this] at hpos₀
    exact lt_irrefl _ hpos₀
  have hcmp : g' < g₀' := by
    change FDLt (ι g') (ι g₀')
    refine fdlt_of_fm_lt (ι_dlab g₀') (ι_dlab g').idNearBot hne₀ ?_ (one_fdlt_ι hpos₀)
    rw [fm_ι_of_version hv₀, fm_ι_of_version hv]
    exact hlt
  rcases hmono with hm | hm
  · have h1 : FDLt 1 (e g') := by simpa using hm 1 g' hpos
    exact hback (mem_fixLeft_of_fdlt (he_dlab g') h1 (hm g' g₀' hcmp) hfix₀)
  · have h1 : FDLt (e g') 1 := by simpa using hm 1 g' hpos
    exact hback (mem_fixLeft_of_fdlt' (he_dlab g') h1 (hm g' g₀' hcmp) hfix₀)

/-- **Main theorem, line form.** Let `e` be an injective homomorphism from `D_K([0,1])` into
Dlab-like homeomorphisms of `ℝ` which preserves or reverses Dlab's order. Then no Dlab-like
homeomorphism `U` induces `α` by conjugation. -/
theorem not_induced_of_dlabLike (e : DlabGroup S.K →* LineAut) (he : Function.Injective e)
    (he_dlab : ∀ g, IsDlabLike (e g))
    (hmono : (∀ f g : DlabGroup S.K, f < g → FDLt (e f) (e g)) ∨
      (∀ f g : DlabGroup S.K, f < g → FDLt (e g) (e f)))
    (U : LineAut) (hU : IsDlabLike U) : ∃ f, e (αo f) ≠ U⁻¹ * e f * U := by
  by_contra h
  push Not at h
  exact source.false_of_induced e he he_dlab (keyProp_of_mono e he_dlab hmono) U hU h

end OrderAut

end Kourovka21149

end

/- ## Section: `Main` -/

section

/-
# Kourovka Notebook Problem 21.149

> **21.149** (V. M. Kopytov, N. Ya. Medvedev). Are there order automorphisms of Dlab groups that
> are not induced by conjugation by elements of a (possibly bigger) Dlab group?
> (Kourovka Notebook, arXiv:1401.0300v46)

We answer the question affirmatively, in the reading of Gong–Yang–Zeng (arXiv:2609.18630): the
smaller Dlab group is embedded into the bigger one by an order-preserving (we also allow
order-reversing) embedding.

For **every** nontrivial slope group `K ≤ ℝ_{>0}` the witness is `G = D_K([0,1])` with Dlab's
order and the order automorphism `αo f = h⁻¹ f h`, where `h` is the alternating-slope
homeomorphism of `Kourovka21149.Conj` (built from a slope `r ∈ K`, `r > 1`).
The bigger group may be any of the six Dlab groups `D_H(I)`, `D_{H*}(I)`, `D_{*H}(I)`,
`\bar D_H(I)`, `D_H`, `D_{H*}` for an **arbitrary** slope subgroup `H ≤ ℝ_{>0}` (of any rank),
equipped with its Dlab order. More generally it may be any group of order automorphisms of
`[0,1]` that are locally right `H`-linear, or any group of locally right `H`-linear order
automorphisms of `ℝ` that are the identity near `-∞`.

## Main results

* `kourovka_21_149`: the answer to Problem 21.149, for every nontrivial slope group `K`.
* `not_induced_interval`, `not_induced_line`: the two forms of the main theorem.
* `αo_not_inner`: in particular `αo` is not inner (the original formulation of the problem).
-/

open Set
open scoped unitInterval Topology

namespace Kourovka21149

open LineAut

/- ## The interval Dlab groups -/

/-- `\bar D_H(I)`: all locally right `H`-linear order automorphisms of `[0, 1]`. -/
def fullIntervalGroup (H : Subgroup NNRealˣ) : Subgroup Dlab.IntervalAut where
  carrier := {f | Dlab.IsLocallyRightHLinear H f}
  one_mem' := (Dlab.isElement_one H).1
  mul_mem' := Dlab.isLocallyRightHLinear_mul
  inv_mem' := Dlab.isLocallyRightHLinear_inv

/-- `D_{H*}(I)`: the elements of `\bar D_H(I)` that are the identity near `0`. -/
def leftIntervalGroup (H : Subgroup NNRealˣ) : Subgroup Dlab.IntervalAut where
  carrier := {f | Dlab.IsLocallyRightHLinear H f ∧ Dlab.IsIdentityNearZero f}
  one_mem' := ⟨(Dlab.isElement_one H).1, (Dlab.isElement_one H).2.1⟩
  mul_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨Dlab.isLocallyRightHLinear_mul hf1 hg1, ?_⟩
    filter_upwards [hf2, hg2] with x hfx hgx
    simp only [RelIso.mul_apply, id_eq, hgx, hfx]
  inv_mem' := by
    rintro f ⟨hf1, hf2⟩
    exact ⟨Dlab.isLocallyRightHLinear_inv hf1, Dlab.isIdentityNearZero_inv hf2⟩

/-- `D_{*H}(I)`: the elements of `\bar D_H(I)` that are the identity near `1`. -/
def rightIntervalGroup (H : Subgroup NNRealˣ) : Subgroup Dlab.IntervalAut where
  carrier := {f | Dlab.IsLocallyRightHLinear H f ∧ Dlab.IsIdentityNearOne f}
  one_mem' := ⟨(Dlab.isElement_one H).1, (Dlab.isElement_one H).2.2⟩
  mul_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨Dlab.isLocallyRightHLinear_mul hf1 hg1, ?_⟩
    filter_upwards [hf2, hg2] with x hfx hgx
    simp only [RelIso.mul_apply, id_eq, hgx, hfx]
  inv_mem' := by
    rintro f ⟨hf1, hf2⟩
    exact ⟨Dlab.isLocallyRightHLinear_inv hf1, Dlab.isIdentityNearOne_inv hf2⟩

/- ## The line Dlab groups -/

/-- Local right `H`-linearity for order automorphisms of `ℝ`. -/
def IsLocallyRightHLinearLine (H : Subgroup NNRealˣ) (a : LineAut) : Prop :=
  ∀ p : ℝ, ∃ ε > 0, ∃ h : H, ∀ x, p < x → x < p + ε → a x = a p + Dlab.slopeToReal h.1 * (x - p)

/-- `a` is the identity on a right ray. -/
def IdNearTop (a : LineAut) : Prop := ∃ c, ∀ x, c ≤ x → a x = x

lemma slopeToReal_pos (h : NNRealˣ) : 0 < Dlab.slopeToReal h := by
  simp [Dlab.slopeToReal]

lemma IsLocallyRightHLinearLine.one (H : Subgroup NNRealˣ) :
    IsLocallyRightHLinearLine H 1 := fun p ↦
  ⟨1, one_pos, 1, fun x _ _ ↦ by simp [Dlab.slopeToReal, one_apply']⟩

lemma IsLocallyRightHLinearLine.mul {H : Subgroup NNRealˣ} {a b : LineAut}
    (ha : IsLocallyRightHLinearLine H a) (hb : IsLocallyRightHLinearLine H b) :
    IsLocallyRightHLinearLine H (a * b) := by
  intro p
  obtain ⟨ε₁, hε₁, h₁, hh₁⟩ := hb p
  obtain ⟨ε₂, hε₂, h₂, hh₂⟩ := ha (b p)
  have hk₁ := slopeToReal_pos h₁.1
  refine ⟨min ε₁ (ε₂ / Dlab.slopeToReal h₁.1), lt_min hε₁ (div_pos hε₂ hk₁), h₂ * h₁,
    fun x hx₁ hx₂ ↦ ?_⟩
  have hbx := hh₁ x hx₁ (by linarith [min_le_left ε₁ (ε₂ / Dlab.slopeToReal h₁.1)])
  have hlt : x - p < ε₂ / Dlab.slopeToReal h₁.1 := by
    linarith [min_le_right ε₁ (ε₂ / Dlab.slopeToReal h₁.1)]
  have hlt' : Dlab.slopeToReal h₁.1 * (x - p) < ε₂ := by
    rw [lt_div_iff₀ hk₁] at hlt; linarith
  have hpos : 0 < Dlab.slopeToReal h₁.1 * (x - p) := mul_pos hk₁ (by linarith)
  have hax := hh₂ (b x) (by rw [hbx]; linarith) (by rw [hbx]; linarith)
  simp only [mul_apply']
  rw [hax, hbx]
  simp only [Dlab.slopeToReal, Subgroup.coe_mul, Units.val_mul, NNReal.coe_mul]
  ring

lemma IsLocallyRightHLinearLine.inv {H : Subgroup NNRealˣ} {a : LineAut}
    (ha : IsLocallyRightHLinearLine H a) : IsLocallyRightHLinearLine H a⁻¹ := by
  intro p
  obtain ⟨ε, hε, h, hh⟩ := ha (a⁻¹ p)
  have hk := slopeToReal_pos h.1
  rw [apply_inv_apply] at hh
  refine ⟨Dlab.slopeToReal h.1 * ε, mul_pos hk hε, h⁻¹, fun y hy₁ hy₂ ↦ ?_⟩
  set x := a⁻¹ p + (y - p) / Dlab.slopeToReal h.1 with hx
  have hx₁ : a⁻¹ p < x := by
    have : 0 < (y - p) / Dlab.slopeToReal h.1 := div_pos (by linarith) hk
    linarith
  have hx₂ : x < a⁻¹ p + ε := by
    have : (y - p) / Dlab.slopeToReal h.1 < ε := by rw [div_lt_iff₀ hk]; linarith
    linarith
  have hax : a x = y := by
    rw [hh x hx₁ hx₂, hx]; field_simp; ring
  have hinv : a⁻¹ y = x := by rw [← hax, inv_apply_apply]
  rw [hinv, hx]
  have : Dlab.slopeToReal (h⁻¹ : H).1 = 1 / Dlab.slopeToReal h.1 := by
    simp [Dlab.slopeToReal]
  rw [this]
  ring

lemma IdNearBot.one : IdNearBot 1 := ⟨0, fun _ _ ↦ rfl⟩

lemma IdNearBot.mul {a b : LineAut} (ha : IdNearBot a) (hb : IdNearBot b) : IdNearBot (a * b) := by
  obtain ⟨c₁, h₁⟩ := ha
  obtain ⟨c₂, h₂⟩ := hb
  refine ⟨min c₁ c₂, fun x hx ↦ ?_⟩
  simp only [mul_apply']
  rw [h₂ x (hx.trans (min_le_right _ _)), h₁ x (hx.trans (min_le_left _ _))]

lemma IdNearBot.inv {a : LineAut} (ha : IdNearBot a) : IdNearBot a⁻¹ := by
  obtain ⟨c, h⟩ := ha
  exact ⟨c, fun x hx ↦ inv_apply_eq_of_apply_eq (h x hx)⟩

lemma IdNearTop.one : IdNearTop 1 := ⟨0, fun _ _ ↦ rfl⟩

lemma IdNearTop.mul {a b : LineAut} (ha : IdNearTop a) (hb : IdNearTop b) : IdNearTop (a * b) := by
  obtain ⟨c₁, h₁⟩ := ha
  obtain ⟨c₂, h₂⟩ := hb
  refine ⟨max c₁ c₂, fun x hx ↦ ?_⟩
  simp only [mul_apply']
  rw [h₂ x ((le_max_right _ _).trans hx), h₁ x ((le_max_left _ _).trans hx)]

lemma IdNearTop.inv {a : LineAut} (ha : IdNearTop a) : IdNearTop a⁻¹ := by
  obtain ⟨c, h⟩ := ha
  exact ⟨c, fun x hx ↦ inv_apply_eq_of_apply_eq (h x hx)⟩

/-- `D_{H*}`: locally right `H`-linear order automorphisms of `ℝ` (equivalently of the extended
line fixing `±∞`) whose support is bounded below. -/
def lineGroupBoundedBelow (H : Subgroup NNRealˣ) : Subgroup LineAut where
  carrier := {a | IsLocallyRightHLinearLine H a ∧ IdNearBot a}
  one_mem' := ⟨IsLocallyRightHLinearLine.one H, IdNearBot.one⟩
  mul_mem' := fun ha hb ↦ ⟨ha.1.mul hb.1, ha.2.mul hb.2⟩
  inv_mem' := fun ha ↦ ⟨ha.1.inv, ha.2.inv⟩

/-- `D_H`: locally right `H`-linear order automorphisms of `ℝ` with bounded support. -/
def lineGroupBounded (H : Subgroup NNRealˣ) : Subgroup LineAut where
  carrier := {a | IsLocallyRightHLinearLine H a ∧ IdNearBot a ∧ IdNearTop a}
  one_mem' := ⟨IsLocallyRightHLinearLine.one H, IdNearBot.one, IdNearTop.one⟩
  mul_mem' := fun ha hb ↦ ⟨ha.1.mul hb.1, ha.2.1.mul hb.2.1, ha.2.2.mul hb.2.2⟩
  inv_mem' := fun ha ↦ ⟨ha.1.inv, ha.2.1.inv, ha.2.2.inv⟩

lemma isDlabLike_of_line {H : Subgroup NNRealˣ} {a : LineAut}
    (ha : IsLocallyRightHLinearLine H a) (hb : IdNearBot a) : IsDlabLike a := by
  refine ⟨hb, fun p _ ↦ ?_⟩
  obtain ⟨ε, hε, h, hh⟩ := ha p
  refine ⟨ε, hε, Dlab.slopeToReal h.1, fun x hx₁ hx₂ ↦ ?_⟩
  rcases hx₁.lt_or_eq with hx₁ | rfl
  · exact hh x hx₁ hx₂
  · ring

/- ## The main theorems -/

section RouteO

variable [S : SlopeChoice]

/-- **Main theorem, interval form.** Let `A` be a group of locally right `H`-linear order
automorphisms of `[0, 1]` (for instance `D_H(I)`, `D_{H*}(I)`, `D_{*H}(I)` or `\bar D_H(I)`,
for any `H`), and let `e : D_K([0,1]) → A` be an embedding preserving or reversing Dlab's
order. Then no element of `A` induces `αo` through `e` by conjugation. -/
theorem not_induced_interval (H : Subgroup NNRealˣ) (A : Subgroup Dlab.IntervalAut)
    (hA : ∀ f ∈ A, Dlab.IsLocallyRightHLinear H f) (e : DlabGroup S.K →* A)
    (he : Function.Injective e)
    (hmono : (∀ f g : DlabGroup S.K, f < g → IntervalFDLt (e f) (e g)) ∨
      (∀ f g : DlabGroup S.K, f < g → IntervalFDLt (e g) (e f)))
    (u : A) : ∃ f, e (αo f) ≠ u⁻¹ * e f * u := by
  set E : DlabGroup S.K →* LineAut := extHom.comp (A.subtype.comp e) with hEdef
  have hE : Function.Injective E := extHom_injective.comp (Subtype.val_injective.comp he)
  have hE_dlab : ∀ g, IsDlabLike (E g) := fun g ↦ isDlabLike_extHom (hA _ (e g).2)
  have hEmono : (∀ f g : DlabGroup S.K, f < g → FDLt (E f) (E g)) ∨
      (∀ f g : DlabGroup S.K, f < g → FDLt (E g) (E f)) := by
    rcases hmono with hm | hm
    · exact Or.inl fun f g hfg ↦ (intervalFDLt_iff _ _).mp (hm f g hfg)
    · exact Or.inr fun f g hfg ↦ (intervalFDLt_iff _ _).mp (hm f g hfg)
  obtain ⟨f, hf⟩ := not_induced_of_dlabLike E hE hE_dlab hEmono (extHom u)
    (isDlabLike_extHom (hA _ u.2))
  refine ⟨f, fun h ↦ hf ?_⟩
  simp only [hEdef, MonoidHom.comp_apply, Subgroup.coe_subtype, h, map_mul, map_inv]

/-- **Main theorem, line form.** Let `A` be a group of locally right `H`-linear order
automorphisms of `ℝ` that are the identity near `-∞` (for instance `D_H` or `D_{H*}`, for any
`H`), and let `e : D_K([0,1]) → A` be an embedding preserving or reversing Dlab's order. Then no
element of `A` induces `αo` through `e` by conjugation. -/
theorem not_induced_line (H : Subgroup NNRealˣ) (A : Subgroup LineAut)
    (hA : ∀ a ∈ A, IsLocallyRightHLinearLine H a ∧ IdNearBot a) (e : DlabGroup S.K →* A)
    (he : Function.Injective e)
    (hmono : (∀ f g : DlabGroup S.K, f < g → FDLt (e f) (e g)) ∨
      (∀ f g : DlabGroup S.K, f < g → FDLt (e g) (e f)))
    (u : A) : ∃ f, e (αo f) ≠ u⁻¹ * e f * u := by
  set E : DlabGroup S.K →* LineAut := A.subtype.comp e with hEdef
  have hE : Function.Injective E := Subtype.val_injective.comp he
  have hE_dlab : ∀ g, IsDlabLike (E g) := fun g ↦
    isDlabLike_of_line (hA _ (e g).2).1 (hA _ (e g).2).2
  obtain ⟨f, hf⟩ := not_induced_of_dlabLike E hE hE_dlab hmono u
    (isDlabLike_of_line (hA _ u.2).1 (hA _ u.2).2)
  refine ⟨f, fun h ↦ hf ?_⟩
  simp only [hEdef, MonoidHom.comp_apply, Subgroup.coe_subtype, h, Subgroup.coe_mul,
    Subgroup.coe_inv]

end RouteO

/-- **Kourovka Notebook Problem 21.149.** For every nontrivial slope group `K` there is an order
automorphism of the Dlab group `D_K([0,1])` (with Dlab's order) which is not induced by
conjugation by an element of any bigger Dlab group, whatever the slope group `H` of the bigger
group, and whatever the order-preserving or order-reversing embedding. -/
theorem kourovka_21_149 (K : Subgroup NNRealˣ) (hK : K ≠ ⊥) :
    ∃ α : DlabGroup K ≃*o DlabGroup K,
      (∀ (H : Subgroup NNRealˣ) (A : Subgroup Dlab.IntervalAut),
        (∀ f ∈ A, Dlab.IsLocallyRightHLinear H f) →
        ∀ e : DlabGroup K →* A, Function.Injective e →
        ((∀ f g : DlabGroup K, f < g → IntervalFDLt (e f) (e g)) ∨
          (∀ f g : DlabGroup K, f < g → IntervalFDLt (e g) (e f))) →
        ∀ u : A, ∃ f, e (α f) ≠ u⁻¹ * e f * u) ∧
      (∀ (H : Subgroup NNRealˣ) (A : Subgroup LineAut),
        (∀ a ∈ A, IsLocallyRightHLinearLine H a ∧ IdNearBot a) →
        ∀ e : DlabGroup K →* A, Function.Injective e →
        ((∀ f g : DlabGroup K, f < g → FDLt (e f) (e g)) ∨
          (∀ f g : DlabGroup K, f < g → FDLt (e g) (e f))) →
        ∀ u : A, ∃ f, e (α f) ≠ u⁻¹ * e f * u) := by
  obtain ⟨S, rfl⟩ := SlopeChoice.exists_of_ne_bot hK
  exact ⟨@αo S, @not_induced_interval S, @not_induced_line S⟩

/- ## The six families -/

lemma mem_dlabSubgroup {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut} (hf : f ∈ Dlab.subgroup H) :
    Dlab.IsLocallyRightHLinear H f := hf.1

/-- The six Dlab groups of Gong–Yang–Zeng satisfy the hypotheses of the main theorems, for any
slope subgroup `H`. -/
theorem six_families (H : Subgroup NNRealˣ) :
    (∀ f ∈ Dlab.subgroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ f ∈ leftIntervalGroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ f ∈ rightIntervalGroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ f ∈ fullIntervalGroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ a ∈ lineGroupBounded H, IsLocallyRightHLinearLine H a ∧ IdNearBot a) ∧
    (∀ a ∈ lineGroupBoundedBelow H, IsLocallyRightHLinearLine H a ∧ IdNearBot a) :=
  ⟨fun _ hf ↦ hf.1, fun _ hf ↦ hf.1, fun _ hf ↦ hf.1, fun _ hf ↦ hf, fun _ ha ↦ ⟨ha.1, ha.2.1⟩,
    fun _ ha ↦ ha⟩

/- ## Consequences and sanity checks -/

section Consequences

variable [S : SlopeChoice]

/-- In particular `αo` is not an inner automorphism (the original formulation of Problem 21.149,
answered in Lean by Monticone et al.). -/
theorem αo_not_inner (u : DlabGroup S.K) : ∃ f, αo f ≠ u⁻¹ * f * u := by
  have := not_induced_interval S.K (Dlab.subgroup S.K) (fun _ hf ↦ hf.1) (MonoidHom.id _)
    Function.injective_id (Or.inl fun f g h ↦ (lt_iff_intervalFDLt f g).mp h) u
  simpa using this

/-- The natural inclusion `D_K([0,1]) ≤ \bar D_H(I)` (for `K ≤ H`) is an injective
order-preserving homomorphism, so the hypotheses of `not_induced_interval` can be met. -/
theorem inclusion_orderPreserving {H : Subgroup NNRealˣ} (hW : S.K ≤ H) :
    ∃ e : DlabGroup S.K →* fullIntervalGroup H, Function.Injective e ∧
      ∀ f g : DlabGroup S.K, f < g → IntervalFDLt (e f) (e g) := by
  refine ⟨Subgroup.inclusion (fun f hf ↦ hf.1.mono hW), Subgroup.inclusion_injective _,
    fun f g h ↦ (lt_iff_intervalFDLt f g).mp h⟩

end Consequences

end Kourovka21149

end

/- ## Section: `Affine` -/

section

/-
# Elements that are affine near `-∞`

The Dlab groups `D_{*H}` and `\bar D_H` on the extended line contain elements that are a
nontrivial affine map `x ↦ k x + t` near `-∞`. We introduce the weaker class `IsDlabLikeAff`
(affine near `-∞`, affine to the right of every fixed point) and show:

* `no_staircase_aff`: such elements still have no infinite descending staircase;
* `idNearBot_of_perfect`: in a perfect group of such elements every element is the identity
  near `-∞`, because the group of affine germs at `-∞` is metabelian.
-/

open Set Filter

namespace Kourovka21149

open LineAut

/-- `a` agrees with an increasing affine map near `-∞`. -/
def AffNearBot (a : LineAut) : Prop :=
  ∃ k t : ℝ, 0 < k ∧ (a : ℝ → ℝ) =ᶠ[atBot] fun x ↦ k * x + t

/-- `a` agrees with a translation near `-∞`. -/
def TransNearBot (a : LineAut) : Prop := ∃ t : ℝ, (a : ℝ → ℝ) =ᶠ[atBot] fun x ↦ x + t

/-- Dlab-like elements in the weak sense: affine near `-∞` and affine to the right of every
fixed point. -/
structure IsDlabLikeAff (a : LineAut) : Prop where
  affNearBot : AffNearBot a
  rightAffine : ∀ p, a p = p → RightAffineAt a p

lemma idNearBot_iff_eventuallyEq {a : LineAut} : IdNearBot a ↔ (a : ℝ → ℝ) =ᶠ[atBot] id := by
  constructor
  · rintro ⟨c, hc⟩
    filter_upwards [eventually_le_atBot c] with x hx using hc x hx
  · intro h
    obtain ⟨c, hc⟩ := eventually_atBot.mp h
    exact ⟨c, hc⟩

lemma IdNearBot.affNearBot {a : LineAut} (h : IdNearBot a) : AffNearBot a := by
  refine ⟨1, 0, one_pos, ?_⟩
  filter_upwards [idNearBot_iff_eventuallyEq.mp h] with x hx
  simp [hx]

lemma IsDlabLike.toAff {a : LineAut} (h : IsDlabLike a) : IsDlabLikeAff a :=
  ⟨h.idNearBot.affNearBot, h.rightAffine⟩

/- ## No staircase -/

theorem no_staircase_aff {u : LineAut} (hu : IsDlabLikeAff u) (z s : ℕ → ℝ)
    (hz : ∀ m, u (z m) = z m) (hs : ∀ m, u (s m) ≠ s m) (h1 : ∀ m, z (m + 1) < s m)
    (h2 : ∀ m, s m < z m) : False := by
  have hdec : ∀ m, z (m + 1) < z m := fun m ↦ (h1 m).trans (h2 m)
  by_cases hbdd : BddBelow (range z)
  · set ζ := ⨅ m, z m with hζ
    have hζle : ∀ m, ζ ≤ z m := fun m ↦ ciInf_le hbdd m
    have hζlt : ∀ m, ζ < z m := fun m ↦ lt_of_le_of_lt (hζle (m + 1)) (hdec m)
    have hfix : u ζ = ζ := by
      rw [hζ, OrderIso.map_ciInf u hbdd]
      simp_rw [hz]
    obtain ⟨ε, hε, k, hk⟩ := hu.rightAffine ζ hfix
    obtain ⟨m, hm⟩ := exists_lt_of_ciInf_lt (show ζ < ζ + ε by linarith)
    have hzm := hk (z m) (hζle m) hm
    rw [hz m, hfix] at hzm
    have hk1 : k = 1 := by
      have hpos : 0 < z m - ζ := by linarith [hζlt m]
      have : (k - 1) * (z m - ζ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have hsm := hk (s m) (by linarith [hζle (m + 1), h1 m]) (by linarith [h2 m])
    rw [hfix, hk1] at hsm
    apply hs m
    rw [hsm]
    ring
  · obtain ⟨k, t, hk, heq⟩ := hu.affNearBot
    obtain ⟨c, hc⟩ := eventually_atBot.mp heq
    have : ∃ m, z m < c := by
      by_contra hcon
      push Not at hcon
      exact hbdd ⟨c, by rintro _ ⟨m, rfl⟩; exact hcon m⟩
    obtain ⟨m, hm⟩ := this
    have hm1 : z (m + 1) < c := (hdec m).trans hm
    -- two fixed points in the affine region force the identity there
    have e1 := hc (z m) hm.le
    have e2 := hc (z (m + 1)) hm1.le
    rw [hz] at e1 e2
    have hk1 : k = 1 := by
      have hpos : 0 < z m - z (m + 1) := by linarith [hdec m]
      have : (k - 1) * (z m - z (m + 1)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have ht : t = 0 := by rw [hk1] at e1; linarith
    have hsm := hc (s m) (by linarith [h2 m])
    rw [hk1, ht] at hsm
    apply hs m
    rw [hsm]
    ring

/- ## Germs at `-∞` -/

lemma tendsto_affine_atBot {k t : ℝ} (hk : 0 < k) :
    Tendsto (fun x : ℝ ↦ k * x + t) atBot atBot :=
  tendsto_atBot_add_const_right _ t (Tendsto.const_mul_atBot hk tendsto_id)

lemma eventuallyEq_mul {a b : LineAut} {A B : ℝ → ℝ} (ha : (a : ℝ → ℝ) =ᶠ[atBot] A)
    (hb : (b : ℝ → ℝ) =ᶠ[atBot] B) (hB : Tendsto B atBot atBot) :
    ((a * b : LineAut) : ℝ → ℝ) =ᶠ[atBot] fun x ↦ A (B x) := by
  filter_upwards [hb, ha.comp_tendsto hB] with x h1 h2
  simp only [mul_apply', Function.comp_apply] at h1 h2 ⊢
  rw [h1, h2]

lemma eventuallyEq_inv {a : LineAut} {A Ainv : ℝ → ℝ} (ha : (a : ℝ → ℝ) =ᶠ[atBot] A)
    (hAinv : ∀ y, A (Ainv y) = y) (hT : Tendsto Ainv atBot atBot) :
    ((a⁻¹ : LineAut) : ℝ → ℝ) =ᶠ[atBot] Ainv := by
  filter_upwards [ha.comp_tendsto hT] with y hy
  simp only [Function.comp_apply] at hy
  rw [hAinv] at hy
  calc a⁻¹ y = a⁻¹ (a (Ainv y)) := by rw [hy]
    _ = Ainv y := inv_apply_apply a _

lemma affNearBot_inv_eq {a : LineAut} {k t : ℝ} (hk : 0 < k)
    (ha : (a : ℝ → ℝ) =ᶠ[atBot] fun x ↦ k * x + t) :
    ((a⁻¹ : LineAut) : ℝ → ℝ) =ᶠ[atBot] fun y ↦ k⁻¹ * y + (-(k⁻¹ * t)) := by
  refine eventuallyEq_inv ha (fun y ↦ ?_) (tendsto_affine_atBot (inv_pos.mpr hk))
  field_simp
  ring

/-- The commutator of two elements that are affine near `-∞` is a translation near `-∞`. -/
lemma transNearBot_commutator {a b : LineAut} (ha : AffNearBot a) (hb : AffNearBot b) :
    TransNearBot (a * b * a⁻¹ * b⁻¹) := by
  obtain ⟨k₁, t₁, hk₁, h₁⟩ := ha
  obtain ⟨k₂, t₂, hk₂, h₂⟩ := hb
  have hi₁ := affNearBot_inv_eq hk₁ h₁
  have hi₂ := affNearBot_inv_eq hk₂ h₂
  have e1 := eventuallyEq_mul h₁ h₂ (tendsto_affine_atBot hk₂)
  have e2 := eventuallyEq_mul e1 hi₁ (tendsto_affine_atBot (inv_pos.mpr hk₁))
  have hT : Tendsto (fun x : ℝ ↦ k₁ * (k₂ * (k₁⁻¹ * x + -(k₁⁻¹ * t₁)) + t₂) + t₁) atBot atBot := by
    have : (fun x : ℝ ↦ k₁ * (k₂ * (k₁⁻¹ * x + -(k₁⁻¹ * t₁)) + t₂) + t₁) =
        fun x ↦ k₂ * x + (k₁ * t₂ + t₁ - k₂ * t₁) := by
      funext x; field_simp; ring
    rw [this]
    exact tendsto_affine_atBot hk₂
  have e3 := eventuallyEq_mul e2 hi₂ (tendsto_affine_atBot (inv_pos.mpr hk₂))
  refine ⟨t₁ + k₁ * t₂ - t₂ - k₂ * t₁, ?_⟩
  filter_upwards [e3] with x hx
  rw [hx]
  field_simp
  ring

lemma TransNearBot.affNearBot {a : LineAut} (h : TransNearBot a) : AffNearBot a := by
  obtain ⟨t, ht⟩ := h
  exact ⟨1, t, one_pos, by filter_upwards [ht] with x hx; rw [hx]; ring⟩

lemma transNearBot_mul {a b : LineAut} (ha : TransNearBot a) (hb : TransNearBot b) :
    TransNearBot (a * b) := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  refine ⟨s + t, ?_⟩
  have := eventuallyEq_mul hs ht (tendsto_atBot_add_const_right _ t tendsto_id)
  filter_upwards [this] with x hx
  rw [hx]; ring

lemma transNearBot_inv {a : LineAut} (ha : TransNearBot a) : TransNearBot a⁻¹ := by
  obtain ⟨s, hs⟩ := ha
  refine ⟨-s, eventuallyEq_inv hs (fun y ↦ by ring) (tendsto_atBot_add_const_right _ _ tendsto_id)⟩

lemma transNearBot_one : TransNearBot 1 := ⟨0, by filter_upwards with x; simp [one_apply']⟩

/-- The commutator of two translations near `-∞` is the identity near `-∞`. -/
lemma idNearBot_commutator {a b : LineAut} (ha : TransNearBot a) (hb : TransNearBot b) :
    (((a * b * a⁻¹ * b⁻¹ : LineAut)) : ℝ → ℝ) =ᶠ[atBot] id := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  have hi₁ := eventuallyEq_inv hs (Ainv := fun y ↦ y + -s) (fun y ↦ by ring)
    (tendsto_atBot_add_const_right _ _ tendsto_id)
  have hi₂ := eventuallyEq_inv ht (Ainv := fun y ↦ y + -t) (fun y ↦ by ring)
    (tendsto_atBot_add_const_right _ _ tendsto_id)
  have e1 := eventuallyEq_mul hs ht (tendsto_atBot_add_const_right _ t tendsto_id)
  have e2 := eventuallyEq_mul e1 hi₁ (tendsto_atBot_add_const_right _ _ tendsto_id)
  have e3 := eventuallyEq_mul e2 hi₂ (tendsto_atBot_add_const_right _ _ tendsto_id)
  filter_upwards [e3] with x hx
  rw [hx]; simp only [id]; ring

lemma eventuallyEq_id_mul {a b : LineAut} (ha : (a : ℝ → ℝ) =ᶠ[atBot] id)
    (hb : (b : ℝ → ℝ) =ᶠ[atBot] id) : ((a * b : LineAut) : ℝ → ℝ) =ᶠ[atBot] id := by
  have := eventuallyEq_mul ha hb tendsto_id
  filter_upwards [this] with x hx
  rw [hx]; rfl

lemma eventuallyEq_id_inv {a : LineAut} (ha : (a : ℝ → ℝ) =ᶠ[atBot] id) :
    ((a⁻¹ : LineAut) : ℝ → ℝ) =ᶠ[atBot] id :=
  eventuallyEq_inv ha (fun _ ↦ rfl) tendsto_id

/-- In a perfect group of elements affine near `-∞`, every element is the identity near `-∞`. -/
theorem idNearBot_of_perfect {Q : Subgroup LineAut} (hperf : Q ≤ ⁅Q, Q⁆)
    (hd : ∀ q ∈ Q, AffNearBot q) {g : LineAut} (hg : g ∈ Q) : IdNearBot g := by
  -- first, every element of `⁅Q, Q⁆` is a translation near `-∞`
  have step1 : ∀ g ∈ ⁅Q, Q⁆, TransNearBot g := by
    intro g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
      rw [commutatorElement_def]
      exact transNearBot_commutator (hd g₁ hg₁) (hd g₂ hg₂)
    | one => exact transNearBot_one
    | mul x y _ _ ihx ihy => exact transNearBot_mul ihx ihy
    | inv x _ ihx => exact transNearBot_inv ihx
  have hQtrans : ∀ q ∈ Q, TransNearBot q := fun q hq ↦ step1 q (hperf hq)
  -- then every element of `⁅Q, Q⁆` is the identity near `-∞`
  have step2 : ∀ g ∈ ⁅Q, Q⁆, ((g : LineAut) : ℝ → ℝ) =ᶠ[atBot] id := by
    intro g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
      rw [commutatorElement_def]
      exact idNearBot_commutator (hQtrans g₁ hg₁) (hQtrans g₂ hg₂)
    | one => filter_upwards with x; rfl
    | mul x y _ _ ihx ihy => exact eventuallyEq_id_mul ihx ihy
    | inv x _ ihx => exact eventuallyEq_id_inv ihx
  exact idNearBot_iff_eventuallyEq.mpr (step2 g (hperf hg))

end Kourovka21149

end

/- ## Section: `Components` -/

section

/-
# Action components of groups of homeomorphisms of the line

For a subgroup `P ≤ LineAut` we consider the open set `Mov P` of points moved by some element of
`P`, and its *first component* `K P`: the points `x ∈ Mov P` such that every fixed point `y ≤ x`
has only fixed points below it.

## Main results

* `K_nonempty`: `K P` is nonempty when `P` acts faithfully on its components through a Dlab-like
  element (via `no_staircase`).
* `mem_K_iff_conj`: transport of `K` under conjugation.
* `K_subset_K_of_le`: nesting.
* `K_disjoint`: two commuting, faithful, perfect groups of Dlab-like homeomorphisms have
  disjoint first components.
-/

open Set

namespace Kourovka21149

open LineAut

variable {P Q : Subgroup LineAut}

/-- The points moved by some element of `P`. -/
def Mov (P : Subgroup LineAut) : Set ℝ := {x | ∃ p ∈ P, p x ≠ x}

/-- The first action component of `P`. -/
def K (P : Subgroup LineAut) : Set ℝ :=
  {x | x ∈ Mov P ∧ ∀ y ≤ x, y ∉ Mov P → ∀ z ≤ y, z ∉ Mov P}

/-- The component of `Mov P` containing `x`. -/
def Comp (P : Subgroup LineAut) (x : ℝ) : Set ℝ := {w | uIcc x w ⊆ Mov P}

lemma not_mem_Mov {x : ℝ} : x ∉ Mov P ↔ ∀ p ∈ P, p x = x := by
  simp [Mov]

lemma K_subset_Mov : K P ⊆ Mov P := fun _ hx ↦ hx.1

lemma apply_mem_Mov {p : LineAut} (hp : p ∈ P) {x : ℝ} (hx : x ∈ Mov P) : p x ∈ Mov P := by
  obtain ⟨q, hq, hqx⟩ := hx
  refine ⟨p * q * p⁻¹, P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp), fun h ↦ hqx ?_⟩
  change p (q (p⁻¹ (p x))) = p x at h
  rw [inv_apply_apply] at h
  exact p.injective h

lemma apply_mem_Mov_iff {p : LineAut} (hp : p ∈ P) {x : ℝ} : p x ∈ Mov P ↔ x ∈ Mov P := by
  refine ⟨fun h ↦ ?_, apply_mem_Mov hp⟩
  have := apply_mem_Mov (P.inv_mem hp) h
  rwa [inv_apply_apply] at this

/-- A moved point below a point of `K P` lies in `K P`. -/
lemma mem_K_of_le {x y : ℝ} (hx : x ∈ K P) (hy : y ∈ Mov P) (hyx : y ≤ x) : y ∈ K P :=
  ⟨hy, fun z hz hzm w hw ↦ hx.2 z (hz.trans hyx) hzm w hw⟩

/-- Points strictly below a point of `K P` and outside `K P` are fixed by `P`. -/
lemma not_mem_Mov_of_lt_K {x z : ℝ} (hx : x ∈ K P) (hz : z ≤ x) (hzK : z ∉ K P) :
    z ∉ Mov P := fun hzM ↦ hzK (mem_K_of_le hx hzM hz)

lemma K_ordConnected {x₁ x₂ y : ℝ} (h₁ : x₁ ∈ K P) (h₂ : x₂ ∈ K P) (hy₁ : x₁ ≤ y) (hy₂ : y ≤ x₂) :
    y ∈ K P := by
  have hyM : y ∈ Mov P := by
    by_contra hyM
    exact (h₂.2 y hy₂ hyM x₁ hy₁) h₁.1
  exact mem_K_of_le h₂ hyM hy₂

lemma apply_mem_K {p : LineAut} (hp : p ∈ P) {x : ℝ} (hx : x ∈ K P) : p x ∈ K P := by
  refine ⟨apply_mem_Mov hp hx.1, fun y hy hyM z hz ↦ ?_⟩
  have hfix : p⁻¹ y = y := (not_mem_Mov.mp hyM) _ (P.inv_mem hp)
  have hyx : y ≤ x := by
    have := p⁻¹.monotone hy
    rwa [hfix, inv_apply_apply] at this
  exact hx.2 y hyx hyM z hz

lemma apply_mem_K_iff {p : LineAut} (hp : p ∈ P) {x : ℝ} : p x ∈ K P ↔ x ∈ K P := by
  refine ⟨fun h ↦ ?_, apply_mem_K hp⟩
  have := apply_mem_K (P.inv_mem hp) h
  rwa [inv_apply_apply] at this

lemma Mov_isOpen_nhd {x : ℝ} (hx : x ∈ Mov P) : ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ Mov P := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hcont : Continuous fun y ↦ p y - y := p.continuous.sub continuous_id
  have hne : p x - x ≠ 0 := sub_ne_zero.mpr hpx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne_fun hcont continuous_const) x hne
  refine ⟨ε, hε, fun y hy ↦ ⟨p, hp, fun h ↦ ?_⟩⟩
  have hyb : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
  have := hball hyb
  simp only [Set.mem_ofPred_eq] at this
  exact this (by rw [h, sub_self])

/-- `K P` is open. -/
lemma K_nhd {x : ℝ} (hx : x ∈ K P) : ∃ ε > 0, Ioo (x - ε) (x + ε) ⊆ K P := by
  obtain ⟨ε, hε, hball⟩ := Mov_isOpen_nhd hx.1
  refine ⟨ε, hε, fun y hy ↦ ⟨hball hy, fun z hz hzM w hw ↦ ?_⟩⟩
  rcases le_or_gt z x with hzx | hzx
  · exact hx.2 z hzx hzM w hw
  · exact absurd (hball ⟨by linarith [hy.1], by linarith [hy.2]⟩) hzM

lemma exists_two_points_K {x : ℝ} (hx : x ∈ K P) : ∃ y ∈ K P, x < y := by
  obtain ⟨ε, hε, h⟩ := K_nhd hx
  exact ⟨x + ε / 2, h ⟨by linarith, by linarith⟩, by linarith⟩

lemma exists_lt_K {x : ℝ} (hx : x ∈ K P) : ∃ y ∈ K P, y < x := by
  obtain ⟨ε, hε, h⟩ := K_nhd hx
  exact ⟨x - ε / 2, h ⟨by linarith, by linarith⟩, by linarith⟩

/- ## Components -/

lemma mem_Comp_self {x : ℝ} (hx : x ∈ Mov P) : x ∈ Comp P x := by
  simp [Comp, hx]

lemma uIcc_apply_subset {p : LineAut} (hp : p ∈ P) {x : ℝ} (hx : x ∈ Mov P) :
    uIcc x (p x) ⊆ Mov P := by
  intro f hf
  by_contra hfM
  have hpf : p f = f := (not_mem_Mov.mp hfM) p hp
  rcases le_total x (p x) with h | h
  · rw [uIcc_of_le h] at hf
    rcases hf.1.lt_or_eq with h1 | rfl
    · rcases hf.2.lt_or_eq with h2 | h2
      · have := p.strictMono h1
        rw [hpf] at this
        exact absurd h2 (not_lt.mpr this.le)
      · exact hfM (by rw [h2]; exact apply_mem_Mov hp hx)
    · exact hfM hx
  · rw [uIcc_of_ge h] at hf
    rcases hf.2.lt_or_eq with h1 | rfl
    · rcases hf.1.lt_or_eq with h2 | h2
      · have := p.strictMono h1
        rw [hpf] at this
        exact absurd h2 (not_lt.mpr this.le)
      · exact hfM (by rw [← h2]; exact apply_mem_Mov hp hx)
    · exact hfM hx

lemma apply_mem_Comp {p : LineAut} (hp : p ∈ P) {x w : ℝ} (hx : x ∈ Mov P)
    (hw : w ∈ Comp P x) : p w ∈ Comp P x := by
  have h1 := uIcc_apply_subset hp hx
  have h2 : uIcc (p x) (p w) ⊆ Mov P := by
    intro g hg
    have hg' : p⁻¹ g ∈ uIcc x w := by
      have hsub := (p⁻¹ : LineAut).monotone.image_uIcc_subset (a := p x) (b := p w)
      rw [inv_apply_apply, inv_apply_apply] at hsub
      exact hsub ⟨g, hg, rfl⟩
    have := apply_mem_Mov hp (hw hg')
    rwa [apply_inv_apply] at this
  intro f hf
  rcases uIcc_subset_uIcc_union_uIcc hf with hf | hf
  · exact h1 hf
  · exact h2 hf

/-- The first component is the component of any of its points. -/
lemma K_eq_Comp {x : ℝ} (hx : x ∈ K P) : K P = Comp P x := by
  ext w
  constructor
  · intro hw f hf
    rcases le_total x w with h | h
    · rw [uIcc_of_le h] at hf
      exact (K_ordConnected hx hw hf.1 hf.2).1
    · rw [uIcc_of_ge h] at hf
      exact (K_ordConnected hw hx hf.1 hf.2).1
  · intro hw
    have hwM : w ∈ Mov P := hw right_mem_uIcc
    rcases le_total w x with h | h
    · exact mem_K_of_le hx hwM h
    · refine ⟨hwM, fun y hy hyM z hz ↦ ?_⟩
      rcases le_total y x with hyx | hyx
      · exact hx.2 y hyx hyM z hz
      · exact absurd (hw (by rw [uIcc_of_le h]; exact ⟨hyx, hy⟩)) hyM

/- ## Faithfulness and nonemptiness -/

/-- `P` acts faithfully on each of its components through the element `p₀`. -/
def FaithfulVia (P : Subgroup LineAut) (p₀ : LineAut) : Prop :=
  ∀ x ∈ Mov P, ∃ w ∈ Comp P x, p₀ w ≠ w

/-- The first component is nonempty. -/
theorem K_nonempty {p₀ : LineAut} (hp₀ : p₀ ∈ P) (hd : IsDlabLikeAff p₀) (hf : FaithfulVia P p₀)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Mov P) : (K P).Nonempty := by
  by_contra hK
  rw [not_nonempty_iff_eq_empty] at hK
  -- for every moved point there is a fixed point below it with a moved point below that
  have step : ∀ x : Mov P, ∃ y z : ℝ, y ≤ (x : ℝ) ∧ y ∉ Mov P ∧ z ≤ y ∧ z ∈ Mov P := by
    rintro ⟨x, hx⟩
    have hxK : x ∉ K P := by rw [hK]; simp
    simp only [K, Set.mem_ofPred_eq, not_and, not_forall, not_not] at hxK
    obtain ⟨y, hy, hyM, z, hz, hzM⟩ := hxK hx
    exact ⟨y, z, hy, hyM, hz, hzM⟩
  choose fy fz hfy hfyM hfz hfzM using step
  let seq : ℕ → Mov P := fun n ↦ Nat.rec ⟨x₀, hx₀⟩ (fun _ x ↦ ⟨fz x, hfzM x⟩) n
  have hseq_succ : ∀ n, (seq (n + 1) : ℝ) = fz (seq n) := fun n ↦ rfl
  set yy : ℕ → ℝ := fun n ↦ fy (seq n) with hyy
  set zz : ℕ → ℝ := fun n ↦ (seq (n + 1) : ℝ) with hzz
  have hzz_lt : ∀ n, zz n < yy n := by
    intro n
    have h1 := hfz (seq n)
    rcases h1.lt_or_eq with h1 | h1
    · simpa [hzz, hyy, hseq_succ] using h1
    · have hm := hfzM (seq n)
      rw [h1] at hm
      exact absurd hm (hfyM (seq n))
  have hyy_lt : ∀ n, yy (n + 1) < zz n := by
    intro n
    have h1 : yy (n + 1) ≤ zz n := hfy (seq (n + 1))
    rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · have hm : zz n ∈ Mov P := (seq (n + 1)).2
      rw [← h1] at hm
      exact absurd hm (hfyM (seq (n + 1)))
  -- faithfulness gives moved points of `p₀` in each gap
  have hw : ∀ n, ∃ w, yy (n + 1) < w ∧ w < yy n ∧ p₀ w ≠ w := by
    intro n
    obtain ⟨w, hwC, hpw⟩ := hf (zz n) (seq (n + 1)).2
    refine ⟨w, ?_, ?_, hpw⟩
    · by_contra hle
      push Not at hle
      have : yy (n + 1) ∈ uIcc (zz n) w := by
        rw [mem_uIcc]; right; exact ⟨hle, (hyy_lt n).le⟩
      exact hfyM (seq (n + 1)) (hwC this)
    · by_contra hle
      push Not at hle
      have : yy n ∈ uIcc (zz n) w := by
        rw [mem_uIcc]; left; exact ⟨(hzz_lt n).le, hle⟩
      exact hfyM (seq n) (hwC this)
  choose ww hww1 hww2 hww3 using hw
  have hfixy : ∀ n, p₀ (yy n) = yy n := fun n ↦ (not_mem_Mov.mp (hfyM (seq n))) p₀ hp₀
  exact no_staircase_aff hd yy ww hfixy hww3 hww1 hww2

/-- A group whose nontrivial elements act nontrivially on every component. -/
def Faithful (P : Subgroup LineAut) : Prop :=
  ∀ x ∈ Mov P, ∀ p ∈ P, p ≠ 1 → ∃ w ∈ Comp P x, p w ≠ w

/-- Faithfulness from a simplicity property of an abstract group. -/
theorem faithful_of_simple {Γ : Type*} [Group Γ] (Qs : Subgroup Γ) (e : Γ →* LineAut)
    (_he : Function.Injective e)
    (hsimple : ∀ N : Subgroup Γ, N ≤ Qs → (∀ q ∈ Qs, ∀ n ∈ N, q * n * q⁻¹ ∈ N) → N ≠ ⊥ → Qs ≤ N) :
    Faithful (Qs.map e) := by
  intro x hx p hp hp1
  obtain ⟨q, hq, rfl⟩ := hp
  by_contra hcon
  push Not at hcon
  -- the kernel of the action on the component of `x`
  let N : Subgroup Γ :=
    { carrier := {g | g ∈ Qs ∧ ∀ w ∈ Comp (Qs.map e) x, e g w = w}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Qs.mul_mem ha hb, fun w hw ↦ ?_⟩
        rw [map_mul, mul_apply', hb' w hw, ha' w hw]
      one_mem' := ⟨Qs.one_mem, fun w _ ↦ by rw [map_one]; rfl⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Qs.inv_mem ha, fun w hw ↦ ?_⟩
        rw [map_inv]
        exact inv_apply_eq_of_apply_eq (ha' w hw) }
  have hqN : q ∈ N := ⟨hq, hcon⟩
  have hN_le : N ≤ Qs := fun g hg ↦ hg.1
  have hN_norm : ∀ a ∈ Qs, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    refine ⟨Qs.mul_mem (Qs.mul_mem ha hn.1) (Qs.inv_mem ha), fun w hw ↦ ?_⟩
    have hmem : e a⁻¹ ∈ Qs.map e := ⟨a⁻¹, Qs.inv_mem ha, rfl⟩
    have hw' : e a⁻¹ w ∈ Comp (Qs.map e) x := apply_mem_Comp hmem hx hw
    rw [map_mul, map_mul, mul_apply', mul_apply', hn.2 _ hw', ← mul_apply', ← map_mul,
      mul_inv_cancel, map_one]
    rfl
  have hN_ne : N ≠ ⊥ := by
    intro h
    have : q ∈ (⊥ : Subgroup Γ) := h ▸ hqN
    rw [Subgroup.mem_bot] at this
    rw [this, map_one] at hp1
    exact hp1 rfl
  have hQN := hsimple N hN_le hN_norm hN_ne
  obtain ⟨r, hr, hrx⟩ := hx
  obtain ⟨g, hg, rfl⟩ := hr
  exact hrx ((hQN hg).2 x (mem_Comp_self ⟨e g, ⟨g, hg, rfl⟩, hrx⟩))

lemma faithfulVia_of_faithful (hP : Faithful P) {p : LineAut} (hp : p ∈ P) (hp1 : p ≠ 1) :
    FaithfulVia P p := fun x hx ↦ hP x hx p hp hp1

/- ## Transport under conjugation -/

lemma mem_Mov_conj_iff (c : LineAut) {P P' : Subgroup LineAut}
    (h : ∀ p, p ∈ P' ↔ c * p * c⁻¹ ∈ P) {x : ℝ} : x ∈ Mov P' ↔ c x ∈ Mov P := by
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨c * p * c⁻¹, (h p).mp hp, fun h' ↦ hpx ?_⟩
    change c (p (c⁻¹ (c x))) = c x at h'
    rw [inv_apply_apply] at h'
    exact c.injective h'
  · rintro ⟨p, hp, hpx⟩
    refine ⟨c⁻¹ * p * c, (h _).mpr (by simpa [mul_assoc] using hp), fun h' ↦ hpx ?_⟩
    change c⁻¹ (p (c x)) = x at h'
    have := congrArg c h'
    rwa [apply_inv_apply] at this

lemma mem_K_conj_iff (c : LineAut) {P P' : Subgroup LineAut}
    (h : ∀ p, p ∈ P' ↔ c * p * c⁻¹ ∈ P) {x : ℝ} : x ∈ K P' ↔ c x ∈ K P := by
  have hM : ∀ y, y ∈ Mov P' ↔ c y ∈ Mov P := fun y ↦ mem_Mov_conj_iff c h
  constructor
  · rintro ⟨hxM, hx⟩
    refine ⟨(hM x).mp hxM, fun y hy hyM z hz hzM ↦ ?_⟩
    have hy' : c⁻¹ y ≤ x := by
      have := c⁻¹.monotone hy; rwa [inv_apply_apply] at this
    have hyM' : c⁻¹ y ∉ Mov P' := by rw [hM, apply_inv_apply]; exact hyM
    have hz' : c⁻¹ z ≤ c⁻¹ y := c⁻¹.monotone hz
    have hzM' : c⁻¹ z ∈ Mov P' := by rw [hM, apply_inv_apply]; exact hzM
    exact hx _ hy' hyM' _ hz' hzM'
  · rintro ⟨hxM, hx⟩
    refine ⟨(hM x).mpr hxM, fun y hy hyM z hz hzM ↦ ?_⟩
    exact hx (c y) (c.monotone hy) (by rw [← hM]; exact hyM) (c z) (c.monotone hz)
      ((hM z).mp hzM)

/- ## Nesting -/

/-- If `P ≤ P'`, `P` is nontrivial and `P'` is faithful, then `K P ⊆ K P'`. -/
theorem K_subset_K_of_le {P P' : Subgroup LineAut} (hle : P ≤ P') (hP'f : Faithful P')
    {p : LineAut} (hp : p ∈ P) (hp1 : p ≠ 1) (hK' : (K P').Nonempty) : K P ⊆ K P' := by
  obtain ⟨x', hx'⟩ := hK'
  obtain ⟨w, hwC, hpw⟩ := hP'f x' hx'.1 p (hle hp) hp1
  have hwK' : w ∈ K P' := by rw [K_eq_Comp hx']; exact hwC
  have hwM : w ∈ Mov P := ⟨p, hp, hpw⟩
  have hMov : Mov P ⊆ Mov P' := fun y ⟨q, hq, hqy⟩ ↦ ⟨q, hle hq, hqy⟩
  intro y hy
  -- first show some point of `K P` lies in `K P'`
  have hxw : ∃ x ∈ K P, x ≤ w := by
    by_contra hcon
    push Not at hcon
    have := not_mem_Mov_of_lt_K hy (le_of_lt (hcon y hy)) ?_
    · exact this hwM
    · intro hwK
      exact lt_irrefl _ (hcon w hwK)
  obtain ⟨x, hxK, hxw⟩ := hxw
  have hxK' : x ∈ K P' := mem_K_of_le hwK' (hMov hxK.1) hxw
  rw [K_eq_Comp hxK']
  intro f hf
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hf
    exact hMov (K_ordConnected hxK hy hf.1 hf.2).1
  · rw [uIcc_of_ge h] at hf
    exact hMov (K_ordConnected hy hxK hf.1 hf.2).1

/- ## Invariant subsets of the first component -/

/-- A nonempty order-connected subset of `K P` invariant under `P` is all of `K P`. -/
theorem eq_K_of_invariant {V : Set ℝ} (hV : V ⊆ K P) (hVne : V.Nonempty)
    (hVc : ∀ x ∈ V, ∀ y ∈ V, ∀ z, x ≤ z → z ≤ y → z ∈ V)
    (hVinv : ∀ p ∈ P, ∀ x, x ∈ V ↔ p x ∈ V) : V = K P := by
  apply le_antisymm hV
  intro w hw
  obtain ⟨v, hv⟩ := hVne
  by_contra hwV
  rcases le_or_gt w v with hwv | hwv
  · -- `w` lies below all of `V`
    have hbelow : ∀ y ∈ V, w < y := by
      intro y hy
      by_contra hle
      push Not at hle
      exact hwV (hVc y hy v hv w hle hwv)
    have hbdd : BddBelow V := ⟨w, fun y hy ↦ (hbelow y hy).le⟩
    set s := sInf V with hs
    have hws : w ≤ s := le_csInf ⟨v, hv⟩ fun y hy ↦ (hbelow y hy).le
    have hsv : s ≤ v := csInf_le hbdd hv
    have hsK : s ∈ K P := K_ordConnected hw (hV hv) hws hsv
    obtain ⟨p, hp, hps⟩ := hsK.1
    apply hps
    have himg : ⇑p '' V = V := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact (hVinv p hp z).mp hz
      · intro hy
        refine ⟨p⁻¹ y, (hVinv p hp _).mpr (by rwa [apply_inv_apply]), apply_inv_apply p y⟩
    rw [hs, OrderIso.map_csInf' p ⟨v, hv⟩ hbdd, himg]
  · -- `w` lies above all of `V`
    have habove : ∀ y ∈ V, y < w := by
      intro y hy
      by_contra hle
      push Not at hle
      exact hwV (hVc v hv y hy w hwv.le hle)
    have hbdd : BddAbove V := ⟨w, fun y hy ↦ (habove y hy).le⟩
    set s := sSup V with hs
    have hsw : s ≤ w := csSup_le ⟨v, hv⟩ fun y hy ↦ (habove y hy).le
    have hvs : v ≤ s := le_csSup hbdd hv
    have hsK : s ∈ K P := K_ordConnected (hV hv) hw hvs hsw
    obtain ⟨p, hp, hps⟩ := hsK.1
    apply hps
    have himg : ⇑p '' V = V := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact (hVinv p hp z).mp hz
      · intro hy
        refine ⟨p⁻¹ y, (hVinv p hp _).mpr (by rwa [apply_inv_apply]), apply_inv_apply p y⟩
    rw [hs, OrderIso.map_csSup' p ⟨v, hv⟩ hbdd, himg]

/- ## Germ triviality for perfect groups -/

/-- The set of elements that are the identity on a right neighbourhood of `a`. -/
def GermTrivialAt (a : ℝ) (g : LineAut) : Prop := ∃ ε > 0, ∀ x, a ≤ x → x < a + ε → g x = x

lemma germTrivialAt_mul {a : ℝ} {g h : LineAut} (hg : GermTrivialAt a g)
    (hh : GermTrivialAt a h) : GermTrivialAt a (g * h) := by
  obtain ⟨ε₁, hε₁, h₁⟩ := hg
  obtain ⟨ε₂, hε₂, h₂⟩ := hh
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx1 hx2 ↦ ?_⟩
  rw [mul_apply', h₂ x hx1 (by linarith [min_le_right ε₁ ε₂]),
    h₁ x hx1 (by linarith [min_le_left ε₁ ε₂])]

lemma germTrivialAt_inv {a : ℝ} {g : LineAut} (hg : GermTrivialAt a g) :
    GermTrivialAt a g⁻¹ := by
  obtain ⟨ε, hε, h⟩ := hg
  exact ⟨ε, hε, fun x hx1 hx2 ↦ inv_apply_eq_of_apply_eq (h x hx1 hx2)⟩

/-- In a perfect group of Dlab-like homeomorphisms fixing `a`, every element is the identity to
the right of `a`. -/
theorem germTrivialAt_of_perfect {a : ℝ} (hperf : P ≤ ⁅P, P⁆) (hfix : ∀ p ∈ P, p a = a)
    (hd : ∀ p ∈ P, IsDlabLikeAff p) {g : LineAut} (hg : g ∈ P) : GermTrivialAt a g := by
  have key : ∀ g ∈ ⁅P, P⁆, GermTrivialAt a g := by
    intro g hg
    rw [Subgroup.commutator_def] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
      obtain ⟨ε, hε, hc⟩ := commutator_eq_self_near (hfix g₁ hg₁) (hfix g₂ hg₂)
        ((hd g₁ hg₁).rightAffine a (hfix g₁ hg₁)) ((hd g₂ hg₂).rightAffine a (hfix g₂ hg₂))
      refine ⟨ε, hε, fun x hx1 hx2 ↦ ?_⟩
      rw [commutatorElement_def]
      exact hc x hx1 hx2
    | one => exact ⟨1, one_pos, fun _ _ _ ↦ rfl⟩
    | mul x y _ _ ihx ihy => exact germTrivialAt_mul ihx ihy
    | inv x _ ihx => exact germTrivialAt_inv ihx
  exact key g (hperf hg)

/- ## Disjointness of first components of commuting groups -/

/-- An order automorphism preserving `Mov P` preserves `K P`. -/
lemma mem_K_iff_of_preserves (c : LineAut) (hc : ∀ y, y ∈ Mov P ↔ c y ∈ Mov P) {x : ℝ} :
    x ∈ K P ↔ c x ∈ K P := by
  constructor
  · rintro ⟨hxM, hx⟩
    refine ⟨(hc x).mp hxM, fun y hy hyM z hz hzM ↦ ?_⟩
    have hy' : c⁻¹ y ≤ x := by
      have := c⁻¹.monotone hy; rwa [inv_apply_apply] at this
    have hyM' : c⁻¹ y ∉ Mov P := by rw [hc, apply_inv_apply]; exact hyM
    have hz' : c⁻¹ z ≤ c⁻¹ y := c⁻¹.monotone hz
    have hzM' : c⁻¹ z ∈ Mov P := by rw [hc, apply_inv_apply]; exact hzM
    exact hx _ hy' hyM' _ hz' hzM'
  · rintro ⟨hxM, hx⟩
    refine ⟨(hc x).mpr hxM, fun y hy hyM z hz hzM ↦ ?_⟩
    exact hx (c y) (c.monotone hy) (by rw [← hc]; exact hyM) (c z) (c.monotone hz)
      ((hc z).mp hzM)

lemma preserves_Mov_of_comm {P Q : Subgroup LineAut} (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    {q : LineAut} (hq : q ∈ Q) : ∀ y, y ∈ Mov P ↔ q y ∈ Mov P := by
  have key : ∀ q ∈ Q, ∀ y, y ∈ Mov P → q y ∈ Mov P := by
    intro q hq y ⟨p, hp, hpy⟩
    refine ⟨p, hp, fun h ↦ hpy ?_⟩
    have hc := congrArg (fun g : LineAut ↦ g y) (hcomm p hp q hq)
    simp only [mul_apply'] at hc
    rw [hc] at h
    exact q.injective h
  intro y
  refine ⟨key q hq y, fun h ↦ ?_⟩
  have := key q⁻¹ (Q.inv_mem hq) _ h
  rwa [inv_apply_apply] at this

/-- **Disjointness.** Let `P` and `Q` be commuting groups of homeomorphisms acting faithfully on
their components, where `Q` is perfect and consists of Dlab-like elements, and `Q` is nontrivial.
Then the first components of `P` and `Q` are disjoint. -/
theorem K_disjoint {P Q : Subgroup LineAut} (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hQf : Faithful Q) (hQperf : Q ≤ ⁅Q, Q⁆) (hQd : ∀ q ∈ Q, IsDlabLikeAff q)
    {q₀ : LineAut} (hq₀ : q₀ ∈ Q) (hq₀1 : q₀ ≠ 1) {x : ℝ} (hxP : x ∈ K P) (hxQ : x ∈ K Q) :
    False := by
  have hcomm' : ∀ q ∈ Q, ∀ p ∈ P, q * p = p * q := fun q hq p hp ↦ (hcomm p hp q hq).symm
  -- `P` preserves `K Q` and `Q` preserves `K P`
  have hPKQ : ∀ p ∈ P, ∀ y, y ∈ K Q ↔ p y ∈ K Q := fun p hp y ↦
    mem_K_iff_of_preserves p (preserves_Mov_of_comm hcomm' hp)
  have hQKP : ∀ q ∈ Q, ∀ y, y ∈ K P ↔ q y ∈ K P := fun q hq y ↦
    mem_K_iff_of_preserves q (preserves_Mov_of_comm hcomm hq)
  -- `K P = K Q`
  set V := K P ∩ K Q with hVdef
  have hVc : ∀ a ∈ V, ∀ b ∈ V, ∀ z, a ≤ z → z ≤ b → z ∈ V := fun a ha b hb z h1 h2 ↦
    ⟨K_ordConnected ha.1 hb.1 h1 h2, K_ordConnected ha.2 hb.2 h1 h2⟩
  have hVP : V = K P := eq_K_of_invariant inter_subset_left ⟨x, hxP, hxQ⟩ hVc
    fun p hp y ↦ ⟨fun hy ↦ ⟨apply_mem_K hp hy.1, (hPKQ p hp y).mp hy.2⟩,
      fun hy ↦ ⟨(apply_mem_K_iff hp).mp hy.1, (hPKQ p hp y).mpr hy.2⟩⟩
  have hVQ : V = K Q := eq_K_of_invariant inter_subset_right ⟨x, hxP, hxQ⟩ hVc
    fun q hq y ↦ ⟨fun hy ↦ ⟨(hQKP q hq y).mp hy.1, apply_mem_K hq hy.2⟩,
      fun hy ↦ ⟨(hQKP q hq y).mpr hy.1, (apply_mem_K_iff hq).mp hy.2⟩⟩
  have hPQ : K P = K Q := hVP.symm.trans hVQ
  -- `q₀` moves a point of the common component
  obtain ⟨w, hwC, hq₀w⟩ := hQf x hxQ.1 q₀ hq₀ hq₀1
  have hwK : w ∈ K Q := by rw [K_eq_Comp hxQ]; exact hwC
  set S := {t | t ∈ K Q ∧ q₀ t ≠ t} with hSdef
  have hSne : S.Nonempty := ⟨w, hwK, hq₀w⟩
  -- `S` is bounded below by a point strictly above the bottom of `K Q`
  have hSb : ∃ b, (∃ k ∈ K Q, k < b) ∧ ∀ t ∈ S, b ≤ t := by
    by_cases hbdd : BddBelow (K Q)
    · set a := sInf (K Q) with ha
      have haK : a ∉ K Q := by
        intro haK
        obtain ⟨y, hyK, hya⟩ := exists_lt_K haK
        exact absurd (csInf_le hbdd hyK) (not_le.mpr hya)
      have hax : a ≤ x := csInf_le hbdd hxQ
      have haM : a ∉ Mov Q := not_mem_Mov_of_lt_K hxQ hax haK
      have hfixa : ∀ q ∈ Q, q a = a := not_mem_Mov.mp haM
      obtain ⟨ε, hε, hgerm⟩ := germTrivialAt_of_perfect hQperf hfixa hQd hq₀
      refine ⟨a + ε, ?_, fun t ht ↦ ?_⟩
      · obtain ⟨k, hkK, hk⟩ := exists_lt_of_csInf_lt ⟨x, hxQ⟩ (show a < a + ε by linarith)
        exact ⟨k, hkK, hk⟩
      · by_contra hlt
        push Not at hlt
        have hat : a ≤ t := csInf_le hbdd ht.1
        exact ht.2 (hgerm t hat hlt)
    · obtain ⟨c₀, hc₀⟩ := idNearBot_of_perfect hQperf (fun q hq ↦ (hQd q hq).affNearBot) hq₀
      refine ⟨c₀, ?_, fun t ht ↦ ?_⟩
      · by_contra hcon
        push Not at hcon
        exact hbdd ⟨c₀, fun k hk ↦ hcon k hk⟩
      · by_contra hlt
        push Not at hlt
        exact ht.2 (hc₀ t hlt.le)
  obtain ⟨b, ⟨k, hkK, hkb⟩, hbS⟩ := hSb
  have hSbdd : BddBelow S := ⟨b, hbS⟩
  set c := sInf S with hc
  have hbc : b ≤ c := le_csInf hSne hbS
  have hcw : c ≤ w := csInf_le hSbdd ⟨hwK, hq₀w⟩
  have hcK : c ∈ K Q := K_ordConnected hkK hwK (by linarith) hcw
  -- every element of `P` fixes `c`
  obtain ⟨p, hp, hpc⟩ := (hPQ ▸ hcK : c ∈ K P).1
  apply hpc
  have himg : ⇑p '' S = S := by
    have hpS : ∀ t, t ∈ S → p t ∈ S := by
      intro t ⟨htK, htm⟩
      refine ⟨(hPKQ p hp t).mp htK, fun h ↦ htm ?_⟩
      have hcq := congrArg (fun g : LineAut ↦ g t) (hcomm p hp q₀ hq₀)
      simp only [mul_apply'] at hcq
      rw [← hcq] at h
      exact p.injective h
    have hpS' : ∀ t, t ∈ S → p⁻¹ t ∈ S := by
      intro t ⟨htK, htm⟩
      refine ⟨(hPKQ p⁻¹ (P.inv_mem hp) t).mp htK, fun h ↦ htm ?_⟩
      have hcq := congrArg (fun g : LineAut ↦ g t) (hcomm p⁻¹ (P.inv_mem hp) q₀ hq₀)
      simp only [mul_apply'] at hcq
      rw [← hcq] at h
      exact p⁻¹.injective h
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩; exact hpS s hs
    · intro ht
      exact ⟨p⁻¹ t, hpS' t ht, apply_inv_apply p t⟩
  rw [hc, OrderIso.map_csInf' p hSne hSbdd, himg]

end Kourovka21149

end

/- ## Section: `Local` -/

section

/-
# Local subgroups of `D_K([0,1])`

For an open interval `(l₁, l₂)` we consider the subgroup `Gc l₁ l₂` of elements whose support
lies in a compact subinterval `[s, t] ⊂ (l₁, l₂)`, and its commutator subgroup `Qc l₁ l₂`.
We prove displacement and compression properties by iterating bumps (with explicit step bounds,
no limits).
-/

open Set

namespace Kourovka21149

open LineAut

/- ## Helpers on `LineAut` -/

lemma commute_of_disjoint (a b : LineAut) (h : ∀ x, a x ≠ x → b x = x) : a * b = b * a := by
  apply RelIso.ext
  intro x
  simp only [mul_apply']
  by_cases hax : a x = x
  · rw [hax]
    by_cases hbx : b x = x
    · rw [hbx, hax]
    · -- `b` moves `x`, so `a` fixes `b x`
      have hbbx : b (b x) ≠ b x := fun h' ↦ hbx (b.injective h')
      have : a (b x) = b x := by
        by_contra hne
        exact hbbx (h (b x) hne)
      exact this
  · have hbx : b x = x := h x hax
    have haax : a (a x) ≠ a x := fun h' ↦ hax (a.injective h')
    rw [hbx, h (a x) haax]

lemma pow_apply (a : LineAut) (n : ℕ) (x : ℝ) : (a ^ n) x = (⇑a)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, mul_apply', ih, Function.iterate_succ_apply]

lemma commutator_self_le {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ ↦ by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)

/- ## Supports in `D_K([0,1])` -/

section Local

variable [S : SlopeChoice]

/-- `g` is supported in `[s, t]`. -/
def SuppIn (g : DlabGroup S.K) (s t : ℝ) : Prop := ∀ x, (x < s ∨ t < x) → ι g x = x

lemma SuppIn.mono {g : DlabGroup S.K} {s t s' t' : ℝ} (h : SuppIn g s t) (hs : s' ≤ s)
    (ht : t ≤ t') : SuppIn g s' t' := by
  intro x hx
  rcases hx with hx | hx
  · exact h x (Or.inl (by linarith))
  · exact h x (Or.inr (by linarith))

lemma SuppIn.one (s t : ℝ) : SuppIn 1 s t := fun x _ ↦ by rw [map_one]; rfl

lemma SuppIn.mul {g g' : DlabGroup S.K} {s t : ℝ} (h : SuppIn g s t) (h' : SuppIn g' s t) :
    SuppIn (g * g') s t := fun x hx ↦ by rw [map_mul, mul_apply', h' x hx, h x hx]

lemma SuppIn.inv {g : DlabGroup S.K} {s t : ℝ} (h : SuppIn g s t) : SuppIn g⁻¹ s t :=
  fun x hx ↦ by rw [map_inv]; exact inv_apply_eq_of_apply_eq (h x hx)

/-- The subgroup of elements supported in `[s, t]`. -/
def SuppGrp (s t : ℝ) : Subgroup (DlabGroup S.K) where
  carrier := {g | SuppIn g s t}
  one_mem' := SuppIn.one s t
  mul_mem' := SuppIn.mul
  inv_mem' := SuppIn.inv

/-- An element supported in `[s, t]` maps `[s, t]` into itself. -/
lemma SuppIn.apply_mem {g : DlabGroup S.K} {s t : ℝ} (h : SuppIn g s t) {x : ℝ}
    (hx : x ∈ Icc s t) : ι g x ∈ Icc s t := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hfix : ι g (ι g x) = ι g x := h _ (Or.inl hlt)
    have := (ι g).injective hfix
    rw [this] at hlt
    linarith [hx.1]
  · by_contra hlt
    push Not at hlt
    have hfix : ι g (ι g x) = ι g x := h _ (Or.inr hlt)
    have := (ι g).injective hfix
    rw [this] at hlt
    linarith [hx.2]

lemma SuppIn.conj {g ρ : DlabGroup S.K} {s t : ℝ} (h : SuppIn g s t) :
    SuppIn (ρ * g * ρ⁻¹) (ι ρ s) (ι ρ t) := by
  intro x hx
  rw [map_mul, map_mul, map_inv, mul_apply', mul_apply']
  have : ι g ((ι ρ)⁻¹ x) = (ι ρ)⁻¹ x := by
    apply h
    rcases hx with hx | hx
    · left
      have := (ι ρ)⁻¹.strictMono hx
      rwa [inv_apply_apply] at this
    · right
      have := (ι ρ)⁻¹.strictMono hx
      rwa [inv_apply_apply] at this
  rw [this, apply_inv_apply]

/-- Elements with disjoint supports `[s, t]` and `[s', t']`, `t < s'`, commute. -/
lemma SuppIn.commute {g g' : DlabGroup S.K} {s t s' t' : ℝ} (h : SuppIn g s t)
    (h' : SuppIn g' s' t') (hts : t < s') : g * g' = g' * g := by
  apply ι_injective
  rw [map_mul, map_mul]
  apply commute_of_disjoint
  intro x hx
  apply h'
  left
  by_contra hle
  push Not at hle
  exact hx (h x (Or.inr (by linarith)))

/-- Elements with disjoint supports commute (general form). -/
lemma commute_of_suppIn_disjoint {g g' : DlabGroup S.K} {s t s' t' : ℝ} (h : SuppIn g s t)
    (h' : SuppIn g' s' t') (hd : t < s' ∨ t' < s) : g * g' = g' * g := by
  rcases hd with hd | hd
  · exact h.commute h' hd
  · exact (h'.commute h hd).symm

/- ## The local groups -/

/-- Elements supported in a compact subinterval of `(l₁, l₂)`. -/
def Gc (l₁ l₂ : ℝ) : Subgroup (DlabGroup S.K) where
  carrier := {g | ∃ s t, l₁ < s ∧ t < l₂ ∧ SuppIn g s t}
  one_mem' := ⟨l₁ + 1, l₂ - 1, by linarith, by linarith, SuppIn.one _ _⟩
  mul_mem' := by
    rintro g g' ⟨s, t, hs, ht, h⟩ ⟨s', t', hs', ht', h'⟩
    refine ⟨min s s', max t t', lt_min hs hs', max_lt ht ht', ?_⟩
    exact (h.mono (min_le_left _ _) (le_max_left _ _)).mul
      (h'.mono (min_le_right _ _) (le_max_right _ _))
  inv_mem' := by
    rintro g ⟨s, t, hs, ht, h⟩
    exact ⟨s, t, hs, ht, h.inv⟩

/-- The local commutator subgroup. -/
noncomputable def Qc (l₁ l₂ : ℝ) : Subgroup (DlabGroup S.K) := ⁅Gc l₁ l₂, Gc l₁ l₂⁆

lemma Qc_le_Gc (l₁ l₂ : ℝ) : Qc l₁ l₂ ≤ Gc l₁ l₂ := commutator_self_le _

lemma Gc_mono {l₁ l₂ m₁ m₂ : ℝ} (h₁ : m₁ ≤ l₁) (h₂ : l₂ ≤ m₂) : Gc l₁ l₂ ≤ Gc m₁ m₂ := by
  rintro g ⟨s, t, hs, ht, h⟩
  exact ⟨s, t, by linarith, by linarith, h⟩

lemma Qc_mono {l₁ l₂ m₁ m₂ : ℝ} (h₁ : m₁ ≤ l₁) (h₂ : l₂ ≤ m₂) : Qc l₁ l₂ ≤ Qc m₁ m₂ :=
  Subgroup.commutator_mono (Gc_mono h₁ h₂) (Gc_mono h₁ h₂)

/-- Every element of `Gc l₁ l₂` has a support interval `[s, t]` with `s ≤ t`. -/
lemma Gc.exists_suppIn {l₁ l₂ : ℝ} (hl : l₁ < l₂) {g : DlabGroup S.K} (hg : g ∈ Gc l₁ l₂) :
    ∃ s t, l₁ < s ∧ s ≤ t ∧ t < l₂ ∧ SuppIn g s t := by
  obtain ⟨s, t, hs, ht, h⟩ := hg
  by_cases hst : s ≤ t
  · exact ⟨s, t, hs, hst, ht, h⟩
  · push Not at hst
    refine ⟨(l₁ + l₂) / 2, (l₁ + l₂) / 2, by linarith, le_rfl, by linarith, fun x _ ↦ ?_⟩
    rcases lt_or_ge x s with hx | hx
    · exact h x (Or.inl hx)
    · exact h x (Or.inr (by linarith))

/-- Elements of `Gc l₁ l₂` with disjoint supports in different local groups commute. -/
lemma Gc_commute {l₁ l₂ m₁ m₂ : ℝ} (hlm : l₂ ≤ m₁) {g g' : DlabGroup S.K} (hg : g ∈ Gc l₁ l₂)
    (hg' : g' ∈ Gc m₁ m₂) : g * g' = g' * g := by
  obtain ⟨s, t, hs, ht, h⟩ := hg
  obtain ⟨s', t', hs', ht', h'⟩ := hg'
  exact h.commute h' (by linarith)

lemma Qc_commute {l₁ l₂ m₁ m₂ : ℝ} (hlm : l₂ ≤ m₁) {g g' : DlabGroup S.K} (hg : g ∈ Qc l₁ l₂)
    (hg' : g' ∈ Qc m₁ m₂) : g * g' = g' * g :=
  Gc_commute hlm (Qc_le_Gc _ _ hg) (Qc_le_Gc _ _ hg')

/-- An element of `Gc l₁ l₂` maps points below `l₂` below `l₂`. -/
lemma Gc.apply_lt {l₁ l₂ : ℝ} {g : DlabGroup S.K} (hg : g ∈ Gc l₁ l₂) {y : ℝ} (hy : y < l₂) :
    ι g y < l₂ := by
  obtain ⟨s, t, hs, ht, h⟩ := hg
  by_cases hyt : t < y
  · rw [h y (Or.inr hyt)]; exact hy
  push Not at hyt
  by_cases hys : y < s
  · rw [h y (Or.inl hys)]; exact hy
  push Not at hys
  have hle : s ≤ t := hys.trans hyt
  exact lt_of_le_of_lt (h.apply_mem ⟨hys, hyt⟩).2 ht

/- ## Bumps as elements of the local groups -/

lemma bumpElt_suppIn {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) :
    SuppIn (bumpElt hp hpq hq) p q := by
  intro x hx
  rw [ι_bumpElt]
  rcases hx with hx | hx
  · exact bumpF_of_le hx.le
  · exact bumpF_of_ge hpq hx.le

lemma bumpElt_mem_Gc {p q l₁ l₂ : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) (hl₁ : l₁ < p)
    (hl₂ : q < l₂) : bumpElt hp hpq hq ∈ Gc l₁ l₂ :=
  ⟨p, q, hl₁, hl₂, bumpElt_suppIn hp hpq hq⟩

lemma ι_bumpElt_inv {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) (x : ℝ) :
    ι (bumpElt hp hpq hq)⁻¹ x = bumpInvF p q x := by
  rw [map_inv]
  apply (ι (bumpElt hp hpq hq)).injective
  rw [apply_inv_apply, ι_bumpElt, bumpF_bumpInvF hpq]

lemma ι_bumpElt_pow {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) (n : ℕ) (x : ℝ) :
    ι (bumpElt hp hpq hq ^ n) x = (bumpF p q)^[n] x := by
  rw [map_pow, pow_apply]
  congr 1
  funext y
  exact ι_bumpElt hp hpq hq y

lemma ι_bumpElt_inv_pow {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q < 1) (n : ℕ) (x : ℝ) :
    ι ((bumpElt hp hpq hq)⁻¹ ^ n) x = (bumpInvF p q)^[n] x := by
  rw [map_pow, pow_apply]
  congr 1
  funext y
  exact ι_bumpElt_inv hp hpq hq y

/- ## Iterating bumps -/

lemma iterate_bumpF_mem {p q : ℝ} (hpq : p < q) {x : ℝ} (hx : x ∈ Ico p q) (n : ℕ) :
    (bumpF p q)^[n] x ∈ Ico p q := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact bumpF_mem_Ico hpq ih

lemma iterate_bumpInvF_mem {p q : ℝ} (hpq : p < q) {x : ℝ} (hx : x ∈ Ioo p q) (n : ℕ) :
    (bumpInvF p q)^[n] x ∈ Ioo p q := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨?_, lt_of_le_of_lt (bumpInvF_le hpq _) ih.2⟩
    calc p = bumpInvF p q p := (bumpInvF_of_le le_rfl).symm
      _ < bumpInvF p q _ := bumpInvF_strictMono hpq ih.1

lemma le_iterate_bumpF {p q : ℝ} (hpq : p < q) (x : ℝ) (n : ℕ) : x ≤ (bumpF p q)^[n] x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_bumpF hpq _)

/-- Iterating a bump pushes `s` beyond any `t < q`. -/
lemma exists_iterate_bumpF_gt {p q s t : ℝ} (hpq : p < q) (hps : p < s) (_hst : s ≤ t)
    (htq : t < q) : ∃ n, t < (bumpF p q)^[n] s := by
  have hr1 : 0 < S.r - 1 := by linarith [S.one_lt_r]
  have hr2 : 0 < 1 - S.r⁻¹ := by linarith [S.inv_r_lt_one]
  set δ := min ((S.r - 1) * (s - p)) ((1 - S.r⁻¹) * (q - t)) with hδ
  have hδpos : 0 < δ := lt_min (mul_pos hr1 (by linarith)) (mul_pos hr2 (by linarith))
  have key : ∀ n : ℕ, t < (bumpF p q)^[n] s ∨ s + n * δ ≤ (bumpF p q)^[n] s := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with ih | ih
      · left
        exact lt_of_lt_of_le ih (le_bumpF hpq _)
      · set y := (bumpF p q)^[n] s with hy
        by_cases hyt : t < y
        · left; exact lt_of_lt_of_le hyt (le_bumpF hpq _)
        · right
          push Not at hyt
          have hy1 : s ≤ y := by
            have : (0 : ℝ) ≤ n * δ := by positivity
            linarith
          have hgap := bumpF_sub_ge (p := p) (q := q) y
          have h1 : δ ≤ min ((S.r - 1) * (y - p)) ((1 - S.r⁻¹) * (q - y)) :=
            le_min ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left (by linarith) hr1.le))
              ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left (by linarith) hr2.le))
          push_cast
          linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) / δ)
  rcases key n with h | h
  · exact ⟨n, h⟩
  · refine ⟨n, ?_⟩
    have : t - s < n * δ := by rwa [div_lt_iff₀ hδpos] at hn
    linarith

/-- Iterating an inverse bump pulls `t` below any `s > p`. -/
lemma exists_iterate_bumpInvF_lt {p q s t : ℝ} (hpq : p < q) (hps : p < s) (_hst : s ≤ t)
    (htq : t < q) : ∃ n, (bumpInvF p q)^[n] t < s := by
  have hr1 : 0 < S.r - 1 := by linarith [S.one_lt_r]
  have hr2 : 0 < 1 - S.r⁻¹ := by linarith [S.inv_r_lt_one]
  set δ := min ((1 - S.r⁻¹) * (s - p)) ((S.r - 1) * (q - t)) with hδ
  have hδpos : 0 < δ := lt_min (mul_pos hr2 (by linarith)) (mul_pos hr1 (by linarith))
  have key : ∀ n : ℕ, (bumpInvF p q)^[n] t < s ∨ (bumpInvF p q)^[n] t ≤ t - n * δ := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with ih | ih
      · left
        exact lt_of_le_of_lt (bumpInvF_le hpq _) ih
      · set y := (bumpInvF p q)^[n] t with hy
        by_cases hys : y < s
        · left; exact lt_of_le_of_lt (bumpInvF_le hpq _) hys
        · right
          push Not at hys
          have hy1 : y ≤ t := by
            have : (0 : ℝ) ≤ n * δ := by positivity
            linarith
          have hgap := bumpInvF_sub_ge (p := p) (q := q) y
          have h1 : δ ≤ min ((1 - S.r⁻¹) * (y - p)) ((S.r - 1) * (q - y)) :=
            le_min ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left (by linarith) hr2.le))
              ((min_le_right _ _).trans (mul_le_mul_of_nonneg_left (by linarith) hr1.le))
          push_cast
          linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - s) / δ)
  rcases key n with h | h
  · exact ⟨n, h⟩
  · refine ⟨n, ?_⟩
    have : t - s < n * δ := by rwa [div_lt_iff₀ hδpos] at hn
    linarith

/- ## Displacement and compression -/

/-- **Displacement.** A compact interval `[s, t] ⊂ (l₁, l₂)` can be moved off itself inside
`Gc l₁ l₂`. -/
lemma exists_displace {l₁ l₂ s t : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : l₂ ≤ 1) (hs : l₁ < s) (hst : s ≤ t)
    (ht : t < l₂) : ∃ γ ∈ Gc l₁ l₂, t < ι γ s := by
  set p := (l₁ + s) / 2 with hpdef
  set q := (t + l₂) / 2 with hqdef
  have hp : 0 < p := by linarith
  have hpq : p < q := by linarith
  have hq : q < 1 := by linarith
  obtain ⟨n, hn⟩ := exists_iterate_bumpF_gt hpq (by linarith : p < s) hst (by linarith : t < q)
  refine ⟨bumpElt hp hpq hq ^ n, Subgroup.pow_mem _ (bumpElt_mem_Gc hp hpq hq
    (by linarith) (by linarith)) n, ?_⟩
  rw [ι_bumpElt_pow]
  exact hn

/-- **Compression.** A compact interval `[s, t] ⊂ (l₁, l₂)` can be mapped into any open interval
`(u₁, u₂) ⊆ (l₁, l₂)` inside `Gc l₁ l₂`. -/
lemma exists_compress {l₁ l₂ s t u₁ u₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl₂ : l₂ ≤ 1) (hs : l₁ < s)
    (hst : s ≤ t) (ht : t < l₂) (hu₁ : l₁ ≤ u₁) (hu : u₁ < u₂) (hu₂ : u₂ ≤ l₂) :
    ∃ ρ ∈ Gc l₁ l₂, u₁ < ι ρ s ∧ ι ρ t < u₂ := by
  set m := (u₁ + u₂) / 2 with hm
  -- first bump: push `s` beyond `m`
  set p₁ := (l₁ + min s m) / 2 with hp₁
  set q₁ := (max t m + l₂) / 2 with hq₁
  have hmin : l₁ < min s m := lt_min hs (by linarith)
  have hmax : max t m < l₂ := max_lt ht (by linarith)
  have hp₁pos : 0 < p₁ := by linarith
  have hp₁s : p₁ < s := by linarith [min_le_left s m]
  have hp₁m : p₁ < m := by linarith [min_le_right s m]
  have htq₁ : t < q₁ := by linarith [le_max_left t m]
  have hmq₁ : m < q₁ := by linarith [le_max_right t m]
  have hpq₁ : p₁ < q₁ := by linarith
  have hq₁1 : q₁ < 1 := by linarith
  obtain ⟨n, hn⟩ := exists_iterate_bumpF_gt hpq₁ hp₁s (le_max_left s m)
    (max_lt (by linarith) hmq₁)
  set b₁ := bumpElt hp₁pos hpq₁ hq₁1 with hb₁
  have hb₁G : b₁ ∈ Gc l₁ l₂ := bumpElt_mem_Gc _ _ _ (by linarith) (by linarith)
  set y₁ := (bumpF p₁ q₁)^[n] s with hy₁
  set y₂ := (bumpF p₁ q₁)^[n] t with hy₂
  have hy₁m : m < y₁ := lt_of_le_of_lt (le_max_right s m) hn
  have hy₂q : y₂ < q₁ := (iterate_bumpF_mem hpq₁ ⟨by linarith, htq₁⟩ n).2
  have hy₁₂ : y₁ ≤ y₂ := by
    have := (show StrictMono (bumpF p₁ q₁)^[n] from (bumpF_strictMono hpq₁).iterate n).monotone hst
    exact this
  -- second bump: pull `t` below `u₂`, keeping `s` above `m`
  have hmpos : 0 < m := by linarith
  set b₂ := bumpElt hmpos hmq₁ hq₁1 with hb₂
  have hb₂G : b₂ ∈ Gc l₁ l₂ := bumpElt_mem_Gc _ _ _ (by linarith) (by linarith)
  have hpull : ∃ k, (bumpInvF m q₁)^[k] y₂ < u₂ := by
    by_cases hy : y₂ < u₂
    · exact ⟨0, hy⟩
    · push Not at hy
      exact exists_iterate_bumpInvF_lt hmq₁ (by linarith) hy hy₂q
  obtain ⟨k, hk⟩ := hpull
  refine ⟨b₂⁻¹ ^ k * b₁ ^ n, (Gc l₁ l₂).mul_mem ((Gc l₁ l₂).pow_mem ((Gc l₁ l₂).inv_mem hb₂G) k)
    ((Gc l₁ l₂).pow_mem hb₁G n), ?_, ?_⟩
  · rw [map_mul, mul_apply', ι_bumpElt_pow, ι_bumpElt_inv_pow]
    have := (iterate_bumpInvF_mem hmq₁ ⟨hy₁m, lt_of_le_of_lt hy₁₂ hy₂q⟩ k).1
    linarith
  · rw [map_mul, mul_apply', ι_bumpElt_pow, ι_bumpElt_inv_pow]
    exact hk

end Local

end Kourovka21149

end

/- ## Section: `Higman` -/

section

/-
# Higman's argument: the local commutator groups are perfect and simple

For `0 ≤ l₁ < l₂ ≤ 1` the group `Qc l₁ l₂ = ⁅Gc l₁ l₂, Gc l₁ l₂⁆` is perfect, and every nontrivial
subgroup of `Qc l₁ l₂` normalised by `Qc l₁ l₂` is all of `Qc l₁ l₂`. The proof follows
G. Higman (1954): displacement gives `⁅α, β⁆ = ⁅⁅α, γ⁆, ⁅β, δ⁆⁆`, and a nontrivial normal element
displaces a small interval, which forces all local commutators into the normal subgroup.
No infinite products are needed.
-/

open Set
open scoped commutatorElement

namespace Kourovka21149

open LineAut

/- ## Commutator identities -/

lemma commutator_mul_left_of_commute {G : Type*} [Group G] {a a' b : G} (h : a' * b = b * a') :
    ⁅a * a', b⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  calc a * a' * b * (a * a')⁻¹ * b⁻¹ = a * (a' * b) * a'⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * a') * a'⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

lemma commutator_mul_right_of_commute {G : Type*} [Group G] {x b b' : G} (h : b' * x = x * b') :
    ⁅x, b * b'⁆ = ⁅x, b⁆ := by
  simp only [commutatorElement_def]
  have h' : b' * x⁻¹ = x⁻¹ * b' := by
    calc b' * x⁻¹ = x⁻¹ * (x * b') * x⁻¹ := by group
      _ = x⁻¹ * (b' * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * b' := by group
  calc x * (b * b') * x⁻¹ * (b * b')⁻¹ = x * b * (b' * x⁻¹) * b'⁻¹ * b⁻¹ := by group
    _ = x * b * (x⁻¹ * b') * b'⁻¹ * b⁻¹ := by rw [h']
    _ = x * b * x⁻¹ * b⁻¹ := by group

lemma commutator_eq_mul_conj {G : Type*} [Group G] (a g : G) : ⁅a, g⁆ = a * (g * a⁻¹ * g⁻¹) := by
  rw [commutatorElement_def]; group

lemma conj_commutator {G : Type*} [Group G] (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]; group

section Higman

variable [S : SlopeChoice]

/- ## Perfectness -/

/-- The local commutator groups are perfect. -/
theorem Qc_perfect {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ < l₂) (hl₂ : l₂ ≤ 1) :
    Qc l₁ l₂ ≤ ⁅Qc l₁ l₂, Qc l₁ l₂⁆ := by
  change ⁅Gc l₁ l₂, Gc l₁ l₂⁆ ≤ ⁅Qc l₁ l₂, Qc l₁ l₂⁆
  rw [Subgroup.commutator_le]
  intro α hα β hβ
  obtain ⟨s₁, t₁, hs₁, hst₁, ht₁, h₁⟩ := Gc.exists_suppIn hl hα
  obtain ⟨s₂, t₂, hs₂, hst₂, ht₂, h₂⟩ := Gc.exists_suppIn hl hβ
  set s := min s₁ s₂ with hsdef
  set t := max t₁ t₂ with htdef
  have hα' : SuppIn α s t := h₁.mono (min_le_left _ _) (le_max_left _ _)
  have hβ' : SuppIn β s t := h₂.mono (min_le_right _ _) (le_max_right _ _)
  have hs : l₁ < s := lt_min hs₁ hs₂
  have ht : t < l₂ := max_lt ht₁ ht₂
  have hst : s ≤ t := (min_le_left _ _).trans (hst₁.trans (le_max_left _ _))
  obtain ⟨γ, hγ, hγs⟩ := exists_displace hl₁ hl₂ hs hst ht
  have hα'supp : SuppIn (γ * α⁻¹ * γ⁻¹) (ι γ s) (ι γ t) := hα'.inv.conj
  have hcomm1 : (γ * α⁻¹ * γ⁻¹) * β = β * (γ * α⁻¹ * γ⁻¹) := (hβ'.commute hα'supp hγs).symm
  have hstep1 : ⁅α, β⁆ = ⁅⁅α, γ⁆, β⁆ := by
    rw [commutator_eq_mul_conj α γ, commutator_mul_left_of_commute hcomm1]
  set t' := ι γ t with ht'def
  have hγst : ι γ s ≤ t' := (ι γ).monotone hst
  have hγt : t ≤ t' := by linarith
  have ht' : t' < l₂ := Gc.apply_lt hγ ht
  have hx : SuppIn ⁅α, γ⁆ s t' := by
    rw [commutator_eq_mul_conj α γ]
    exact (hα'.mono le_rfl hγt).mul (hα'supp.mono (by linarith) le_rfl)
  obtain ⟨δ, hδ, hδs⟩ := exists_displace hl₁ hl₂ hs (hst.trans hγt) ht'
  have hβ'supp : SuppIn (δ * β⁻¹ * δ⁻¹) (ι δ s) (ι δ t) := hβ'.inv.conj
  have hcomm2 : (δ * β⁻¹ * δ⁻¹) * ⁅α, γ⁆ = ⁅α, γ⁆ * (δ * β⁻¹ * δ⁻¹) :=
    (hx.commute hβ'supp hδs).symm
  have hstep2 : ⁅⁅α, γ⁆, β⁆ = ⁅⁅α, γ⁆, ⁅β, δ⁆⁆ := by
    rw [commutator_eq_mul_conj β δ, commutator_mul_right_of_commute hcomm2]
  rw [hstep1, hstep2]
  exact Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator hα hγ)
    (Subgroup.commutator_mem_commutator hβ hδ)

/- ## Simplicity -/

/-- A nontrivial element displaces a small interval around a moved point. -/
lemma exists_displaced_interval (n : DlabGroup S.K) {x₀ : ℝ} (hx₀ : ι n x₀ ≠ x₀) {l₁ l₂ : ℝ}
    (h₁ : l₁ < x₀) (h₂ : x₀ < l₂) :
    ∃ r > 0, l₁ < x₀ - r ∧ x₀ + r < l₂ ∧
      ∀ y, x₀ - r ≤ y → y ≤ x₀ + r → (ι n y < x₀ - r ∨ x₀ + r < ι n y) := by
  set d := |ι n x₀ - x₀| with hd
  have hdpos : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hx₀)
  obtain ⟨r₀, hr₀, hcont⟩ := Metric.continuous_iff.mp (ι n).continuous x₀ (d / 3) (by linarith)
  set r := min (r₀ / 2) (min (d / 3) (min ((x₀ - l₁) / 2) ((l₂ - x₀) / 2))) with hr
  have hr1 : r ≤ r₀ / 2 := min_le_left _ _
  have hr2 : r ≤ d / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ (x₀ - l₁) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr4 : r ≤ (l₂ - x₀) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrpos : 0 < r := lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  refine ⟨r, hrpos, by linarith, by linarith, fun y hy1 hy2 ↦ ?_⟩
  have hyd : dist y x₀ < r₀ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  have hclose := hcont y hyd
  rw [Real.dist_eq] at hclose
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have : |ι n x₀ - x₀| ≤ |ι n y - ι n x₀| + |ι n y - x₀| := by
    calc |ι n x₀ - x₀| = |(ι n y - x₀) - (ι n y - ι n x₀)| := by ring_nf
      _ ≤ |ι n y - x₀| + |ι n y - ι n x₀| := abs_sub _ _
      _ = |ι n y - ι n x₀| + |ι n y - x₀| := add_comm _ _
  have h3 : |ι n y - x₀| ≤ r := by rw [abs_le]; constructor <;> linarith
  rw [← hd] at this
  linarith

/-- **Simplicity (Higman).** A nontrivial subgroup of `Qc l₁ l₂` normalised by `Qc l₁ l₂`
contains `Qc l₁ l₂`. -/
theorem Qc_simple {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ < l₂) (hl₂ : l₂ ≤ 1)
    (N : Subgroup (DlabGroup S.K)) (hNle : N ≤ Qc l₁ l₂)
    (hNnorm : ∀ q ∈ Qc l₁ l₂, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hN : N ≠ ⊥) : Qc l₁ l₂ ≤ N := by
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra h
    push Not at h
    exact hN ((Subgroup.eq_bot_iff_forall N).mpr h)
  obtain ⟨sn, tn, hsn, _, htn, hnsupp⟩ := Gc.exists_suppIn hl (Qc_le_Gc _ _ (hNle hnN))
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ι n x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hn1 (ι_injective (by rw [map_one]; exact eq_one_iff.mpr h))
  have hx₀s : sn ≤ x₀ := by
    by_contra h; push Not at h; exact hx₀ (hnsupp x₀ (Or.inl h))
  have hx₀t : x₀ ≤ tn := by
    by_contra h; push Not at h; exact hx₀ (hnsupp x₀ (Or.inr h))
  obtain ⟨r, hr, hr₁, hr₂, hdisp⟩ :=
    exists_displaced_interval n hx₀ (show l₁ < x₀ by linarith) (show x₀ < l₂ by linarith)
  set u₁ := x₀ - r with hu₁
  set u₂ := x₀ + r with hu₂
  have hu : u₁ < u₂ := by linarith
  -- Claim A: `Qc u₁ u₂ ≤ N`
  have hA : Qc u₁ u₂ ≤ N := by
    refine (Qc_perfect (by linarith) hu (by linarith)).trans ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haL : a ∈ Qc l₁ l₂ := Qc_mono (by linarith) (by linarith) ha
    have hbL : b ∈ Qc l₁ l₂ := Qc_mono (by linarith) (by linarith) hb
    obtain ⟨sa, ta, hsa, hsta, hta, hasupp⟩ := Gc.exists_suppIn hu (Qc_le_Gc _ _ ha)
    obtain ⟨sb, tb, hsb, _, htb, hbsupp⟩ := Gc.exists_suppIn hu (Qc_le_Gc _ _ hb)
    -- the conjugate `n a⁻¹ n⁻¹` is supported outside `[u₁, u₂]`
    have hside : ι n ta < u₁ ∨ u₂ < ι n sa := by
      rcases hdisp sa hsa.le (by linarith) with h1 | h1 <;>
        rcases hdisp ta (by linarith) hta.le with h2 | h2
      · exact Or.inl h2
      · exfalso
        have hy1 : sa ≤ (ι n)⁻¹ x₀ := by
          have := (ι n)⁻¹.monotone (show ι n sa ≤ x₀ by linarith)
          rwa [inv_apply_apply] at this
        have hy2 : (ι n)⁻¹ x₀ ≤ ta := by
          have := (ι n)⁻¹.monotone (show x₀ ≤ ι n ta by linarith)
          rwa [inv_apply_apply] at this
        have hd := hdisp ((ι n)⁻¹ x₀) (by linarith) (by linarith)
        rw [apply_inv_apply] at hd
        rcases hd with h | h <;> linarith
      · exfalso
        have := (ι n).monotone hsta
        linarith
      · exact Or.inr h1
    have ha'supp : SuppIn (n * a⁻¹ * n⁻¹) (ι n sa) (ι n ta) := hasupp.inv.conj
    have hcomm : (n * a⁻¹ * n⁻¹) * b = b * (n * a⁻¹ * n⁻¹) := by
      rcases hside with h | h
      · exact commute_of_suppIn_disjoint ha'supp hbsupp (Or.inl (by linarith))
      · exact commute_of_suppIn_disjoint ha'supp hbsupp (Or.inr (by linarith))
    have heq : ⁅a, b⁆ = ⁅⁅a, n⁆, b⁆ := by
      rw [commutator_eq_mul_conj a n, commutator_mul_left_of_commute hcomm]
    have hanN : ⁅a, n⁆ ∈ N := by
      rw [commutatorElement_def]
      exact N.mul_mem (hNnorm a haL n hnN) (N.inv_mem hnN)
    rw [heq, commutatorElement_def]
    have h1 := hNnorm b hbL _ (N.inv_mem hanN)
    have h2 := N.mul_mem hanN h1
    simpa [mul_assoc] using h2
  -- Claim B: every local commutator lies in `N`
  change ⁅Gc l₁ l₂, Gc l₁ l₂⁆ ≤ N
  rw [Subgroup.commutator_le]
  intro α hα β hβ
  obtain ⟨s₁, t₁, hs₁, hst₁, ht₁, h₁⟩ := Gc.exists_suppIn hl hα
  obtain ⟨s₂, t₂, hs₂, hst₂, ht₂, h₂⟩ := Gc.exists_suppIn hl hβ
  set s := min s₁ s₂
  set t := max t₁ t₂
  have hα' : SuppIn α s t := h₁.mono (min_le_left _ _) (le_max_left _ _)
  have hβ' : SuppIn β s t := h₂.mono (min_le_right _ _) (le_max_right _ _)
  have hs : l₁ < s := lt_min hs₁ hs₂
  have ht : t < l₂ := max_lt ht₁ ht₂
  have hst : s ≤ t := (min_le_left _ _).trans (hst₁.trans (le_max_left _ _))
  obtain ⟨ρ, hρ, hρs, hρt⟩ :=
    exists_compress hl₁ hl₂ hs hst ht (show l₁ ≤ u₁ by linarith) hu (show u₂ ≤ l₂ by linarith)
  obtain ⟨sρ, tρ, hsρ, hstρ, htρ, hρsupp⟩ := Gc.exists_suppIn hl hρ
  set S₀ := min s sρ
  set T₀ := max t tρ
  have hS : l₁ < S₀ := lt_min hs hsρ
  have hT : T₀ < l₂ := max_lt ht htρ
  have hST : S₀ ≤ T₀ := (min_le_left _ _).trans (hst.trans (le_max_left _ _))
  obtain ⟨τ, hτ, hτS⟩ := exists_displace hl₁ hl₂ hS hST hT
  have hρ' : SuppIn ρ⁻¹ S₀ T₀ := (hρsupp.mono (min_le_right _ _) (le_max_right _ _)).inv
  have hσsupp : SuppIn (τ * ρ⁻¹ * τ⁻¹) (ι τ S₀) (ι τ T₀) := hρ'.conj
  have hσα : (τ * ρ⁻¹ * τ⁻¹) * α = α * (τ * ρ⁻¹ * τ⁻¹) :=
    commute_of_suppIn_disjoint hσsupp hα' (Or.inr (lt_of_le_of_lt (le_max_left t tρ) hτS))
  have hσβ : (τ * ρ⁻¹ * τ⁻¹) * β = β * (τ * ρ⁻¹ * τ⁻¹) :=
    commute_of_suppIn_disjoint hσsupp hβ' (Or.inr (lt_of_le_of_lt (le_max_left t tρ) hτS))
  set σ := τ * ρ⁻¹ * τ⁻¹ with hσdef
  have hρ'eq : ⁅ρ, τ⁆ = ρ * σ := commutator_eq_mul_conj ρ τ
  have hρ'Q : ⁅ρ, τ⁆ ∈ Qc l₁ l₂ := Subgroup.commutator_mem_commutator hρ hτ
  have hconjα : ⁅ρ, τ⁆ * α * ⁅ρ, τ⁆⁻¹ = ρ * α * ρ⁻¹ := by
    rw [hρ'eq]
    calc ρ * σ * α * (ρ * σ)⁻¹ = ρ * (σ * α) * σ⁻¹ * ρ⁻¹ := by group
      _ = ρ * (α * σ) * σ⁻¹ * ρ⁻¹ := by rw [hσα]
      _ = ρ * α * ρ⁻¹ := by group
  have hconjβ : ⁅ρ, τ⁆ * β * ⁅ρ, τ⁆⁻¹ = ρ * β * ρ⁻¹ := by
    rw [hρ'eq]
    calc ρ * σ * β * (ρ * σ)⁻¹ = ρ * (σ * β) * σ⁻¹ * ρ⁻¹ := by group
      _ = ρ * (β * σ) * σ⁻¹ * ρ⁻¹ := by rw [hσβ]
      _ = ρ * β * ρ⁻¹ := by group
  have hραU : ρ * α * ρ⁻¹ ∈ Gc u₁ u₂ := ⟨ι ρ s, ι ρ t, hρs, hρt, hα'.conj⟩
  have hρβU : ρ * β * ρ⁻¹ ∈ Gc u₁ u₂ := ⟨ι ρ s, ι ρ t, hρs, hρt, hβ'.conj⟩
  have hin : ⁅ρ, τ⁆ * ⁅α, β⁆ * ⁅ρ, τ⁆⁻¹ ∈ N := by
    rw [conj_commutator, hconjα, hconjβ]
    exact hA (Subgroup.commutator_mem_commutator hραU hρβU)
  have := hNnorm _ ((Qc l₁ l₂).inv_mem hρ'Q) _ hin
  have key : ∀ c x : DlabGroup S.K, c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := fun c x ↦ by group
  rwa [key] at this

/-- The local commutator groups are nontrivial. -/
lemma Qc_nontrivial {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ < l₂) (hl₂ : l₂ ≤ 1) :
    ∃ q ∈ Qc l₁ l₂, q ≠ 1 := by
  obtain ⟨a, b, p, q, hp, hq, hlow, hhigh, hab⟩ :=
    exists_noncomm ((2 * l₁ + l₂) / 3) ((l₁ + 2 * l₂) / 3) (by linarith) (by linarith)
      (by linarith)
  have haG : a ∈ Gc l₁ l₂ := ⟨p, q, by linarith, by linarith, fun x hx ↦ by
    rcases hx with hx | hx
    · exact (hlow x hx).1
    · exact (hhigh x hx).1⟩
  have hbG : b ∈ Gc l₁ l₂ := ⟨p, q, by linarith, by linarith, fun x hx ↦ by
    rcases hx with hx | hx
    · exact (hlow x hx).2
    · exact (hhigh x hx).2⟩
  refine ⟨⁅a, b⁆, Subgroup.commutator_mem_commutator haG hbG, fun h ↦ hab ?_⟩
  rw [commutatorElement_def] at h
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

end Higman

end Kourovka21149

end

/- ## Section: `RouteI` -/

section

/-
# Arbitrary injective embeddings

We show that `α` is not induced by conjugation through **any** injective homomorphism
`e : D_K([0,1]) → LineAut` into Dlab-like homeomorphisms; no order assumption is made.

For an interval `L = (l₁, l₂)` let `P L = e (Qc L)` and let `K L` be its first action component.
By Higman simplicity the groups `P L` act faithfully on their components, so:
- `K L` is nonempty;
- `K` is monotone in `L`;
- `K L` and `K M` are disjoint when `L` and `M` are;
- `K` is transported by `U`.

The two intervals `(0, τ)` and `(τ, 1)` always have the same orientation. In the
orientation-preserving case the function `w τ = sup K (0, τ)` gives an infinite descending
staircase for `U` from the fixed points of `h` near `0`. In the orientation-reversing case the
function `sup K (τ, 1)` does so from the fixed points near `1`.
-/

open Set
open scoped commutatorElement

namespace Kourovka21149

open LineAut

/- ## Relative position of disjoint components -/

/-- Every point of `A` lies to the left of every point of `B`. -/
def Before (A B : Set ℝ) : Prop := ∀ x ∈ A, ∀ y ∈ B, x < y

lemma before_or_before {P Q : Subgroup LineAut} {a b : ℝ} (ha : a ∈ K P) (hb : b ∈ K Q)
    (hdisj : ∀ x, x ∈ K P → x ∉ K Q) : Before (K P) (K Q) ∨ Before (K Q) (K P) := by
  have hab : a ≠ b := fun h ↦ hdisj a ha (h ▸ hb)
  rcases lt_or_gt_of_ne hab with h | h
  · left
    intro x hx y hy
    by_contra hle
    push Not at hle
    rcases le_or_gt y a with hya | hya
    · exact hdisj a ha (K_ordConnected hy hb hya h.le)
    · exact hdisj y (K_ordConnected ha hx hya.le hle) hy
  · right
    intro y hy x hx
    by_contra hle
    push Not at hle
    rcases le_or_gt x b with hxb | hxb
    · exact hdisj b (K_ordConnected hx ha hxb h.le) hb
    · exact hdisj x hx (K_ordConnected hb hy hxb.le hle)

lemma not_before_of_before {A B : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) (h : Before A B) :
    ¬ Before B A := by
  intro h'
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact lt_asymm (h a ha b hb) (h' b hb a ha)

/- ## The staircase -/

lemma false_of_staircase' {U : LineAut} (hU : IsDlabLikeAff U) (z s : ℕ → ℝ)
    (hz : ∀ m, U (z m) = z m) (hs : ∀ m, U (s m) ≠ s m) (h₁ : ∀ m, z (m + 1) ≤ s m)
    (h₂ : ∀ m, s m ≤ z m) : False := by
  refine no_staircase_aff hU z s hz hs (fun m ↦ ?_) (fun m ↦ ?_)
  · rcases (h₁ m).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hz (m + 1)) (hs m)
  · rcases (h₂ m).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hz m) (hs m)

section RouteI

variable [S : SlopeChoice]

/- ## Transport of local groups under `α` -/

lemma extHom_hAut_inv (y : ℝ) : (extHom hAut)⁻¹ y = hInvF y := by
  apply (extHom hAut).injective
  rw [apply_inv_apply, extHom_hAut, hF_hInvF]

lemma hInvF_strictMono : StrictMono hInvF := by
  intro x y hxy
  have := (extHom hAut)⁻¹.strictMono hxy
  rwa [extHom_hAut_inv, extHom_hAut_inv] at this

lemma ι_α_symm (g : DlabGroup S.K) : ι (α.symm g) = extHom hAut * ι g * (extHom hAut)⁻¹ := by
  have h := ι_α (α.symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]; group

lemma suppIn_α {g : DlabGroup S.K} {s t : ℝ} (h : SuppIn g s t) :
    SuppIn (α g) (hInvF s) (hInvF t) := by
  intro x hx
  rw [ι_α, mul_apply', mul_apply', extHom_hAut, extHom_hAut_inv]
  have : ι g (hF x) = hF x := by
    apply h
    rcases hx with hx | hx
    · left; have := hF_strictMono hx; rwa [hF_hInvF] at this
    · right; have := hF_strictMono hx; rwa [hF_hInvF] at this
  rw [this, hInvF_hF]

lemma suppIn_α_symm {g : DlabGroup S.K} {s t : ℝ} (h : SuppIn g s t) :
    SuppIn (α.symm g) (hF s) (hF t) := by
  intro x hx
  rw [ι_α_symm, mul_apply', mul_apply', extHom_hAut, extHom_hAut_inv]
  have : ι g (hInvF x) = hInvF x := by
    apply h
    rcases hx with hx | hx
    · left; have := hInvF_strictMono hx; rwa [hInvF_hF] at this
    · right; have := hInvF_strictMono hx; rwa [hInvF_hF] at this
  rw [this, hF_hInvF]

lemma mem_Gc_α_iff {l₁ l₂ : ℝ} {g : DlabGroup S.K} :
    α g ∈ Gc (hInvF l₁) (hInvF l₂) ↔ g ∈ Gc l₁ l₂ := by
  constructor
  · rintro ⟨s, t, hs, ht, h⟩
    have h' := suppIn_α_symm h
    rw [MulEquiv.symm_apply_apply] at h'
    refine ⟨hF s, hF t, ?_, ?_, h'⟩
    · have := hF_strictMono hs; rwa [hF_hInvF] at this
    · have := hF_strictMono ht; rwa [hF_hInvF] at this
  · rintro ⟨s, t, hs, ht, h⟩
    exact ⟨hInvF s, hInvF t, hInvF_strictMono hs, hInvF_strictMono ht, suppIn_α h⟩

lemma Gc_map_α (l₁ l₂ : ℝ) :
    (Gc l₁ l₂).map α.toMonoidHom = Gc (hInvF l₁) (hInvF l₂) := by
  ext g
  constructor
  · rintro ⟨g₀, hg₀, rfl⟩
    exact mem_Gc_α_iff.mpr hg₀
  · intro hg
    refine ⟨α.symm g, ?_, by simp⟩
    show α.symm g ∈ Gc l₁ l₂
    rw [← mem_Gc_α_iff, MulEquiv.apply_symm_apply]; exact hg

lemma Qc_map_α (l₁ l₂ : ℝ) :
    (Qc l₁ l₂).map α.toMonoidHom = Qc (hInvF l₁) (hInvF l₂) := by
  unfold Qc
  rw [Subgroup.map_commutator, Gc_map_α]

lemma mem_Qc_α_iff {l₁ l₂ : ℝ} {g : DlabGroup S.K} :
    α g ∈ Qc (hInvF l₁) (hInvF l₂) ↔ g ∈ Qc l₁ l₂ := by
  rw [← Qc_map_α]
  constructor
  · rintro ⟨g₀, hg₀, h⟩
    have : g₀ = g := α.injective h
    rw [← this]; exact hg₀
  · intro hg; exact ⟨g, hg, rfl⟩

lemma hInvF_zero : hInvF 0 = 0 := hInvF_of_nonpos le_rfl

lemma hInvF_one : hInvF 1 = 1 := hInvF_of_one_le le_rfl

lemma hInvF_X (m : ℕ) : hInvF (X m) = X m := by
  conv_lhs => rw [← hF_X m]
  exact hInvF_hF _

lemma hInvF_Y (m : ℕ) : hInvF (Y m) = Y m := by
  conv_lhs => rw [← hF_Y m]
  exact hInvF_hF _

/- ## The target groups -/

section Target

variable (e : DlabGroup S.K →* LineAut)

/-- The image of the local commutator group of `(l₁, l₂)`. -/
noncomputable def PL (l₁ l₂ : ℝ) : Subgroup LineAut := (Qc l₁ l₂).map e

variable {e}

/-- Standing hypotheses on the interval. -/
structure GoodInterval (l₁ l₂ : ℝ) : Prop where
  nonneg : 0 ≤ l₁
  lt : l₁ < l₂
  le_one : l₂ ≤ 1

lemma PL_faithful (he : Function.Injective e) {l₁ l₂ : ℝ} (hL : GoodInterval l₁ l₂) :
    Faithful (PL e l₁ l₂) :=
  faithful_of_simple _ e he fun N hN hnorm hne ↦ Qc_simple hL.1 hL.2 hL.3 N hN hnorm hne

lemma PL_perfect {l₁ l₂ : ℝ} (hL : GoodInterval l₁ l₂) :
    PL e l₁ l₂ ≤ ⁅PL e l₁ l₂, PL e l₁ l₂⁆ := by
  unfold PL
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (Qc_perfect hL.1 hL.2 hL.3)

lemma PL_dlab (he_dlab : ∀ g, IsDlabLikeAff (e g)) (l₁ l₂ : ℝ) :
    ∀ p ∈ PL e l₁ l₂, IsDlabLikeAff p := by
  rintro p ⟨q, _, rfl⟩; exact he_dlab q

lemma PL_nontrivial (he : Function.Injective e) {l₁ l₂ : ℝ} (hL : GoodInterval l₁ l₂) :
    ∃ p ∈ PL e l₁ l₂, p ≠ 1 := by
  obtain ⟨q, hq, hq1⟩ := Qc_nontrivial hL.1 hL.2 hL.3
  exact ⟨e q, ⟨q, hq, rfl⟩, fun h ↦ hq1 (he (by rw [h, map_one]))⟩

lemma K_PL_nonempty (he : Function.Injective e) (he_dlab : ∀ g, IsDlabLikeAff (e g))
    {l₁ l₂ : ℝ} (hL : GoodInterval l₁ l₂) : (K (PL e l₁ l₂)).Nonempty := by
  obtain ⟨p, hp, hp1⟩ := PL_nontrivial he hL
  obtain ⟨x₀, hx₀⟩ : ∃ x, p x ≠ x := by
    by_contra h; push Not at h; exact hp1 (eq_one_iff.mpr h)
  exact K_nonempty hp (PL_dlab he_dlab _ _ p hp)
    (faithfulVia_of_faithful (PL_faithful he hL) hp hp1) ⟨p, hp, hx₀⟩

lemma K_PL_mono (he : Function.Injective e) (he_dlab : ∀ g, IsDlabLikeAff (e g))
    {l₁ l₂ m₁ m₂ : ℝ} (hL : GoodInterval l₁ l₂) (hM : GoodInterval m₁ m₂) (h₁ : l₁ ≤ m₁)
    (h₂ : m₂ ≤ l₂) : K (PL e m₁ m₂) ⊆ K (PL e l₁ l₂) := by
  obtain ⟨p, hp, hp1⟩ := PL_nontrivial he hM
  exact K_subset_K_of_le (Subgroup.map_mono (Qc_mono h₁ h₂)) (PL_faithful he hL) hp hp1
    (K_PL_nonempty he he_dlab hL)

lemma K_PL_disjoint (he : Function.Injective e) (he_dlab : ∀ g, IsDlabLikeAff (e g))
    {l₁ l₂ m₁ m₂ : ℝ} (hM : GoodInterval m₁ m₂) (hlm : l₂ ≤ m₁ ∨ m₂ ≤ l₁) {x : ℝ}
    (hx : x ∈ K (PL e l₁ l₂)) (hx' : x ∈ K (PL e m₁ m₂)) : False := by
  obtain ⟨q, hq, hq1⟩ := PL_nontrivial he hM
  have hcomm : ∀ p ∈ PL e l₁ l₂, ∀ q ∈ PL e m₁ m₂, p * q = q * p := by
    rintro p ⟨a, ha, rfl⟩ q ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    rcases hlm with hlm | hlm
    · rw [Qc_commute hlm ha hb]
    · rw [(Qc_commute hlm hb ha).symm]
  exact K_disjoint hcomm (PL_faithful he hM) (PL_perfect hM) (PL_dlab he_dlab _ _) hq hq1 hx hx'

lemma mem_K_PL_α {U : LineAut} (hu : ∀ f, e (α f) = U⁻¹ * e f * U) {l₁ l₂ x : ℝ} :
    x ∈ K (PL e (hInvF l₁) (hInvF l₂)) ↔ U x ∈ K (PL e l₁ l₂) := by
  apply mem_K_conj_iff U
  intro p
  constructor
  · rintro ⟨q', hq', rfl⟩
    obtain ⟨q, rfl⟩ : ∃ q, α q = q' := ⟨α.symm q', by simp⟩
    have hq'' : α q ∈ Qc (hInvF l₁) (hInvF l₂) := hq'
    rw [mem_Qc_α_iff] at hq''
    refine ⟨q, hq'', ?_⟩
    rw [hu q]; group
  · rintro ⟨q, hq, hpq⟩
    refine ⟨α q, mem_Qc_α_iff.mpr hq, ?_⟩
    rw [hu q, hpq]; group

lemma K_PL_α_eq {U : LineAut} (hu : ∀ f, e (α f) = U⁻¹ * e f * U) (l₁ l₂ : ℝ) :
    K (PL e (hInvF l₁) (hInvF l₂)) = ⇑(U⁻¹ : LineAut) '' K (PL e l₁ l₂) := by
  ext x
  rw [mem_K_PL_α hu]
  constructor
  · intro h; exact ⟨U x, h, inv_apply_apply U x⟩
  · rintro ⟨y, hy, rfl⟩; rwa [apply_inv_apply]

end Target

/-- **Main theorem for injective embeddings.** No Dlab-like homeomorphism induces `α` through an
injective homomorphism into Dlab-like homeomorphisms. -/
theorem false_of_induced_injective (e : DlabGroup S.K →* LineAut) (he : Function.Injective e)
    (he_dlab : ∀ g, IsDlabLikeAff (e g)) (U : LineAut) (hU : IsDlabLikeAff U)
    (hu : ∀ f, e (α f) = U⁻¹ * e f * U) : False := by
  -- notation
  set K0 : ℝ → Set ℝ := fun τ ↦ K (PL e 0 τ) with hK0
  set K1 : ℝ → Set ℝ := fun τ ↦ K (PL e τ 1) with hK1
  have good0 : ∀ τ, 0 < τ → τ ≤ 1 → GoodInterval 0 τ := fun τ h1 h2 ↦ ⟨le_rfl, h1, h2⟩
  have good1 : ∀ τ, 0 ≤ τ → τ < 1 → GoodInterval τ 1 := fun τ h1 h2 ↦ ⟨h1, h2, le_rfl⟩
  have ne0 : ∀ τ, 0 < τ → τ ≤ 1 → (K0 τ).Nonempty := fun τ h1 h2 ↦
    K_PL_nonempty he he_dlab (good0 τ h1 h2)
  have ne1 : ∀ τ, 0 ≤ τ → τ < 1 → (K1 τ).Nonempty := fun τ h1 h2 ↦
    K_PL_nonempty he he_dlab (good1 τ h1 h2)
  have disj : ∀ τ, 0 < τ → τ < 1 → ∀ x, x ∈ K0 τ → x ∉ K1 τ := fun τ h1 h2 x hx hx' ↦
    K_PL_disjoint he he_dlab (good1 τ h1.le h2) (Or.inl le_rfl) hx hx'
  have mono0 : ∀ τ τ', 0 < τ → τ ≤ τ' → τ' ≤ 1 → K0 τ ⊆ K0 τ' := fun τ τ' h1 h2 h3 ↦
    K_PL_mono he he_dlab (good0 τ' (by linarith) h3) (good0 τ h1 (by linarith)) le_rfl h2
  have mono1 : ∀ τ τ', 0 ≤ τ → τ ≤ τ' → τ' < 1 → K1 τ' ⊆ K1 τ := fun τ τ' h1 h2 h3 ↦
    K_PL_mono he he_dlab (good1 τ h1 (by linarith)) (good1 τ' (by linarith) h3) h2 le_rfl
  -- orientation at `1/2`
  obtain ⟨a, ha⟩ := ne0 (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨b, hb⟩ := ne1 (1 / 2) (by norm_num) (by norm_num)
  have hhalf := before_or_before ha hb (disj (1 / 2) (by norm_num) (by norm_num))
  -- the orientation is the same for every cut
  have orient : ∀ τ, 0 < τ → τ < 1 →
      (Before (K0 (1 / 2)) (K1 (1 / 2)) → Before (K0 τ) (K1 τ)) ∧
      (Before (K1 (1 / 2)) (K0 (1 / 2)) → Before (K1 τ) (K0 τ)) := by
    intro τ h1 h2
    obtain ⟨x, hx⟩ := ne0 τ h1 h2.le
    obtain ⟨y, hy⟩ := ne1 τ h1.le h2
    have hcut := before_or_before hx hy (disj τ h1 h2)
    rcases le_total τ (1 / 2) with hτ | hτ
    · have hs0 : K0 τ ⊆ K0 (1 / 2) := mono0 τ (1 / 2) h1 hτ (by norm_num)
      have hs1 : K1 (1 / 2) ⊆ K1 τ := mono1 τ (1 / 2) h1.le hτ (by norm_num)
      constructor
      · intro hB
        rcases hcut with hc | hc
        · exact hc
        · exfalso
          have h' : Before (K1 (1 / 2)) (K0 τ) := fun u hu v hv ↦ hc u (hs1 hu) v hv
          have h'' : Before (K0 τ) (K1 (1 / 2)) := fun u hu v hv ↦ hB u (hs0 hu) v hv
          exact not_before_of_before ⟨x, hx⟩ ⟨b, hb⟩ h'' h'
      · intro hB
        rcases hcut with hc | hc
        · exfalso
          have h' : Before (K0 τ) (K1 (1 / 2)) := fun u hu v hv ↦ hc u hu v (hs1 hv)
          have h'' : Before (K1 (1 / 2)) (K0 τ) := fun u hu v hv ↦ hB u hu v (hs0 hv)
          exact not_before_of_before ⟨x, hx⟩ ⟨b, hb⟩ h' h''
        · exact hc
    · have hs0 : K0 (1 / 2) ⊆ K0 τ := mono0 (1 / 2) τ (by norm_num) hτ h2.le
      have hs1 : K1 τ ⊆ K1 (1 / 2) := mono1 (1 / 2) τ (by norm_num) hτ h2
      constructor
      · intro hB
        rcases hcut with hc | hc
        · exact hc
        · exfalso
          have h' : Before (K1 τ) (K0 (1 / 2)) := fun u hu v hv ↦ hc u hu v (hs0 hv)
          have h'' : Before (K0 (1 / 2)) (K1 τ) := fun u hu v hv ↦ hB u hu v (hs1 hv)
          exact not_before_of_before ⟨a, ha⟩ ⟨y, hy⟩ h'' h'
      · intro hB
        rcases hcut with hc | hc
        · exfalso
          have h' : Before (K0 (1 / 2)) (K1 τ) := fun u hu v hv ↦ hc u (hs0 hu) v hv
          have h'' : Before (K1 τ) (K0 (1 / 2)) := fun u hu v hv ↦ hB u (hs1 hu) v hv
          exact not_before_of_before ⟨a, ha⟩ ⟨y, hy⟩ h' h''
        · exact hc
  -- small middle intervals
  have goodM : ∀ β γ, 0 < β → β < γ → γ < 1 →
      GoodInterval (β + (γ - β) / 3) (β + 2 * (γ - β) / 3) := fun β γ h1 h2 h3 ↦
    ⟨by linarith, by linarith, by linarith⟩
  rcases hhalf with hplus | hminus
  · ------------------------------------------------------------------
    -- orientation preserving: use `w τ = sup K (0, τ)` and the fixed points `X m`
    have hB : ∀ τ, 0 < τ → τ < 1 → Before (K0 τ) (K1 τ) := fun τ h1 h2 ↦
      (orient τ h1 h2).1 hplus
    have bdd : ∀ τ, 0 < τ → τ < 1 → BddAbove (K0 τ) := by
      intro τ h1 h2
      obtain ⟨y, hy⟩ := ne1 τ h1.le h2
      exact ⟨y, fun x hx ↦ (hB τ h1 h2 x hx y hy).le⟩
    set w : ℝ → ℝ := fun τ ↦ sSup (K0 τ) with hw
    have w_mono : ∀ τ τ', 0 < τ → τ ≤ τ' → τ' < 1 → w τ ≤ w τ' := fun τ τ' h1 h2 h3 ↦
      csSup_le_csSup (bdd τ' (by linarith) h3) (ne0 τ h1 (by linarith))
        (mono0 τ τ' h1 h2 h3.le)
    have w_transport : ∀ τ, 0 < τ → τ < 1 → w (hInvF τ) = U⁻¹ (w τ) := by
      intro τ h1 h2
      have hset : K0 (hInvF τ) = ⇑(U⁻¹ : LineAut) '' K0 τ := by
        have := K_PL_α_eq (e := e) hu 0 τ
        rwa [hInvF_zero] at this
      simp only [hw]
      rw [hset]
      exact (OrderIso.map_csSup' U⁻¹ (ne0 τ h1 h2.le) (bdd τ h1 h2)).symm
    have w_ne : ∀ β γ, 0 < β → β < γ → γ < 1 → w β ≠ w γ := by
      intro β γ h1 h2 h3 hwe
      obtain ⟨y, hy⟩ := K_PL_nonempty he he_dlab (goodM β γ h1 h2 h3)
      obtain ⟨y', hy', hyy'⟩ := exists_two_points_K hy
      -- `K M` lies to the right of `K (0, β)`
      have hMsub1 : K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)) ⊆ K1 β :=
        K_PL_mono he he_dlab (good1 β h1.le (by linarith)) (goodM β γ h1 h2 h3)
          (by linarith) (by linarith)
      have hMsub0 : K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)) ⊆ K0 γ :=
        K_PL_mono he he_dlab (good0 γ (by linarith) h3.le) (goodM β γ h1 h2 h3)
          (by linarith) (by linarith)
      have hlow : ∀ z ∈ K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)), w β ≤ z := by
        intro z hz
        exact csSup_le (ne0 β h1 (by linarith)) fun x hx ↦
          (hB β h1 (by linarith) x hx z (hMsub1 hz)).le
      have hhigh : ∀ z ∈ K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)), z ≤ w γ := by
        intro z hz
        exact le_csSup (bdd γ (by linarith) h3) (hMsub0 hz)
      have e1 := hlow y hy
      have e2 := hhigh y' hy'
      rw [hwe] at e1
      linarith
    -- the staircase from the fixed points `X m`
    set τm : ℕ → ℝ := fun m ↦ (X (m + 1) + X m) / 2 with hτm
    set βm : ℕ → ℝ := fun m ↦ hInvF (τm m) with hβm
    have hX1 : ∀ m, X (m + 1) < τm m := fun m ↦ by simp only [hτm]; linarith [X_succ_lt m]
    have hX2 : ∀ m, τm m < X m := fun m ↦ by simp only [hτm]; linarith [X_succ_lt m]
    have hβ1 : ∀ m, X (m + 1) < βm m := fun m ↦ by
      have := hInvF_strictMono (hX1 m); rwa [hInvF_X] at this
    have hβ2 : ∀ m, βm m < X m := fun m ↦ by
      have := hInvF_strictMono (hX2 m); rwa [hInvF_X] at this
    have hβτ : ∀ m, βm m < τm m := fun m ↦ by
      have := lt_hF (hβ1 m) (hβ2 m)
      simp only [hβm, hF_hInvF] at this
      exact this
    have hXlt1 : ∀ m, X m < 1 := fun m ↦ lt_of_le_of_lt (X_le_half m) (by norm_num)
    have hz : ∀ m, U (w (X m)) = w (X m) := by
      intro m
      have := w_transport (X m) (X_pos m) (hXlt1 m)
      rw [hInvF_X] at this
      have h2 := congrArg U this
      rw [apply_inv_apply] at h2
      exact h2
    have hs : ∀ m, U (w (βm m)) ≠ w (βm m) := by
      intro m h
      have ht := w_transport (τm m) ((X_pos (m + 1)).trans (hX1 m))
        ((hX2 m).trans (hXlt1 m))
      have hβw : w (βm m) = U⁻¹ (w (τm m)) := ht
      rw [hβw, apply_inv_apply] at h
      exact w_ne (βm m) (τm m) ((X_pos (m + 1)).trans (hβ1 m)) (hβτ m)
        ((hX2 m).trans (hXlt1 m)) (hβw.trans h.symm)
    exact false_of_staircase' hU (fun m ↦ w (X m)) (fun m ↦ w (βm m)) hz hs
      (fun m ↦ w_mono _ _ (X_pos (m + 1)) (hβ1 m).le ((hβ2 m).trans (hXlt1 m)))
      (fun m ↦ w_mono _ _ ((X_pos (m + 1)).trans (hβ1 m)) (hβ2 m).le (hXlt1 m))
  · ------------------------------------------------------------------
    -- orientation reversing: use `w τ = sup K (τ, 1)` and the fixed points `Y m`
    have hB : ∀ τ, 0 < τ → τ < 1 → Before (K1 τ) (K0 τ) := fun τ h1 h2 ↦
      (orient τ h1 h2).2 hminus
    have bdd : ∀ τ, 0 < τ → τ < 1 → BddAbove (K1 τ) := by
      intro τ h1 h2
      obtain ⟨y, hy⟩ := ne0 τ h1 h2.le
      exact ⟨y, fun x hx ↦ (hB τ h1 h2 x hx y hy).le⟩
    set w : ℝ → ℝ := fun τ ↦ sSup (K1 τ) with hw
    have w_anti : ∀ τ τ', 0 < τ → τ ≤ τ' → τ' < 1 → w τ' ≤ w τ := fun τ τ' h1 h2 h3 ↦
      csSup_le_csSup (bdd τ h1 (by linarith)) (ne1 τ' (by linarith) h3)
        (mono1 τ τ' h1.le h2 h3)
    have w_transport : ∀ τ, 0 < τ → τ < 1 → w (hInvF τ) = U⁻¹ (w τ) := by
      intro τ h1 h2
      have hset : K1 (hInvF τ) = ⇑(U⁻¹ : LineAut) '' K1 τ := by
        have := K_PL_α_eq (e := e) hu τ 1
        rwa [hInvF_one] at this
      simp only [hw]
      rw [hset]
      exact (OrderIso.map_csSup' U⁻¹ (ne1 τ h1.le h2) (bdd τ h1 h2)).symm
    have w_ne : ∀ β γ, 0 < β → β < γ → γ < 1 → w β ≠ w γ := by
      intro β γ h1 h2 h3 hwe
      obtain ⟨y, hy⟩ := K_PL_nonempty he he_dlab (goodM β γ h1 h2 h3)
      obtain ⟨y', hy', hyy'⟩ := exists_two_points_K hy
      have hMsub1 : K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)) ⊆ K1 β :=
        K_PL_mono he he_dlab (good1 β h1.le (by linarith)) (goodM β γ h1 h2 h3)
          (by linarith) (by linarith)
      have hMsub0 : K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)) ⊆ K0 γ :=
        K_PL_mono he he_dlab (good0 γ (by linarith) h3.le) (goodM β γ h1 h2 h3)
          (by linarith) (by linarith)
      -- `K M` lies to the right of `K (γ, 1)` and inside `K (β, 1)`
      have hlow : ∀ z ∈ K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)), w γ ≤ z := by
        intro z hz
        exact csSup_le (ne1 γ (by linarith) h3) fun x hx ↦
          (hB γ (by linarith) h3 x hx z (hMsub0 hz)).le
      have hhigh : ∀ z ∈ K (PL e (β + (γ - β) / 3) (β + 2 * (γ - β) / 3)), z ≤ w β := by
        intro z hz
        exact le_csSup (bdd β h1 (by linarith)) (hMsub1 hz)
      have e1 := hlow y hy
      have e2 := hhigh y' hy'
      rw [← hwe] at e1
      linarith
    -- the staircase from the fixed points `Y m`
    set τm : ℕ → ℝ := fun m ↦ (Y m + Y (m + 1)) / 2 with hτm
    set βm : ℕ → ℝ := fun m ↦ hInvF (τm m) with hβm
    have hY1 : ∀ m, Y m < τm m := fun m ↦ by simp only [hτm]; linarith [Y_lt_succ m]
    have hY2 : ∀ m, τm m < Y (m + 1) := fun m ↦ by simp only [hτm]; linarith [Y_lt_succ m]
    have hβ1 : ∀ m, Y m < βm m := fun m ↦ by
      have := hInvF_strictMono (hY1 m); rwa [hInvF_Y] at this
    have hβ2 : ∀ m, βm m < Y (m + 1) := fun m ↦ by
      have := hInvF_strictMono (hY2 m); rwa [hInvF_Y] at this
    have hβτ : ∀ m, βm m < τm m := fun m ↦ by
      have := lt_hF_R (hβ1 m) (hβ2 m)
      simp only [hβm, hF_hInvF] at this
      exact this
    have hYpos : ∀ m, 0 < Y m := fun m ↦ by linarith [half_le_Y m]
    have hz : ∀ m, U (w (Y m)) = w (Y m) := by
      intro m
      have := w_transport (Y m) (hYpos m) (Y_lt_one m)
      rw [hInvF_Y] at this
      have h2 := congrArg U this
      rw [apply_inv_apply] at h2
      exact h2
    have hs : ∀ m, U (w (βm m)) ≠ w (βm m) := by
      intro m h
      have ht := w_transport (τm m) ((hYpos m).trans (hY1 m)) ((hY2 m).trans (Y_lt_one _))
      have hβw : w (βm m) = U⁻¹ (w (τm m)) := ht
      rw [hβw, apply_inv_apply] at h
      exact w_ne (βm m) (τm m) ((hYpos m).trans (hβ1 m)) (hβτ m)
        ((hY2 m).trans (Y_lt_one _)) (hβw.trans h.symm)
    exact false_of_staircase' hU (fun m ↦ w (Y m)) (fun m ↦ w (βm m)) hz hs
      (fun m ↦ w_anti _ _ ((hYpos m).trans (hβ1 m)) (hβ2 m).le (Y_lt_one _))
      (fun m ↦ w_anti _ _ (hYpos m) (hβ1 m).le ((hβ2 m).trans (Y_lt_one _)))

/-- **Main theorem, injective form.** For any injective homomorphism `e` from `D_K([0,1])` into
Dlab-like homeomorphisms of `ℝ`, and any Dlab-like `U`, `U` does not induce `αo` through `e`. -/
theorem not_induced_injective_line (e : DlabGroup S.K →* LineAut) (he : Function.Injective e)
    (he_dlab : ∀ g, IsDlabLikeAff (e g)) (U : LineAut) (hU : IsDlabLikeAff U) :
    ∃ f, e (αo f) ≠ U⁻¹ * e f * U := by
  by_contra h
  push Not at h
  exact false_of_induced_injective e he he_dlab U hU h

end RouteI

end Kourovka21149

end

/- ## Section: `MainInjective` -/

section

/-
# Kourovka 21.149 for arbitrary embeddings

The strongest form of the answer. For every nontrivial slope group `K`, the order automorphism
`αo` of `D_K([0,1])` is not induced by conjugation through **any** injective homomorphism `e`
into a bigger group. The bigger group may be any group of locally right `H`-linear order
automorphisms of `[0,1]`, or of `ℝ` with elements that are affine near `-∞`, for any slope
subgroup `H` of any rank. No order assumption is made on `e` or on the bigger group.

This covers the six Dlab groups `D_H(I)`, `D_{H*}(I)`, `D_{*H}(I)`, `\bar D_H(I)`, `D_H` and `D_{H*}`
of Gong–Yang–Zeng, and the two groups `lineGroupBoundedAbove H` and `lineGroupFull H` of
automorphisms of `ℝ` that are `H`-affine near `-∞` (`families_satisfy_hypotheses`).

The condition at `-∞` cannot be dropped for this `αo`. Conjugating `h` by a piecewise-linear
homeomorphism `(0, 1) → (-∞, 0)` gives a locally right `K`-linear automorphism of `ℝ` whose
support is bounded above and which induces `αo` through an injective, order-preserving embedding
into `D_H` (for `H ⊇ K ∪ {2}`). This remark is not formalized.
-/

open Set Filter

namespace Kourovka21149

open LineAut

/- ## The two remaining Dlab groups on the extended line -/

/-- `a` agrees near `-∞` with an affine map whose slope lies in `H` (local right `H`-linearity at
`-∞` on the extended line). -/
def AffNearBotH (H : Subgroup NNRealˣ) (a : LineAut) : Prop :=
  ∃ h : H, ∃ t : ℝ, (a : ℝ → ℝ) =ᶠ[atBot] fun x ↦ Dlab.slopeToReal h.1 * x + t

lemma AffNearBotH.affNearBot {H : Subgroup NNRealˣ} {a : LineAut} (h : AffNearBotH H a) :
    AffNearBot a := by
  obtain ⟨h, t, ht⟩ := h
  exact ⟨_, t, slopeToReal_pos h.1, ht⟩

lemma AffNearBotH.one (H : Subgroup NNRealˣ) : AffNearBotH H 1 :=
  ⟨1, 0, by filter_upwards with x; simp [Dlab.slopeToReal, one_apply']⟩

lemma AffNearBotH.mul {H : Subgroup NNRealˣ} {a b : LineAut} (ha : AffNearBotH H a)
    (hb : AffNearBotH H b) : AffNearBotH H (a * b) := by
  obtain ⟨h₁, t₁, e₁⟩ := ha
  obtain ⟨h₂, t₂, e₂⟩ := hb
  refine ⟨h₁ * h₂, Dlab.slopeToReal h₁.1 * t₂ + t₁, ?_⟩
  have := eventuallyEq_mul e₁ e₂ (tendsto_affine_atBot (slopeToReal_pos h₂.1))
  filter_upwards [this] with x hx
  rw [hx]
  simp only [Dlab.slopeToReal, Subgroup.coe_mul, Units.val_mul, NNReal.coe_mul]
  ring

lemma AffNearBotH.inv {H : Subgroup NNRealˣ} {a : LineAut} (ha : AffNearBotH H a) :
    AffNearBotH H a⁻¹ := by
  obtain ⟨h, t, e⟩ := ha
  refine ⟨h⁻¹, -((Dlab.slopeToReal h.1)⁻¹ * t), ?_⟩
  have := affNearBot_inv_eq (slopeToReal_pos h.1) e
  filter_upwards [this] with x hx
  rw [hx]
  simp [Dlab.slopeToReal]

/-- The locally right `H`-linear order automorphisms of `ℝ` that are `H`-affine near `-∞`. This is
a version of `\bar D_H` on the extended line with a condition at `-∞`; see the module
docstring. -/
def lineGroupFull (H : Subgroup NNRealˣ) : Subgroup LineAut where
  carrier := {a | IsLocallyRightHLinearLine H a ∧ AffNearBotH H a}
  one_mem' := ⟨IsLocallyRightHLinearLine.one H, AffNearBotH.one H⟩
  mul_mem' := fun ha hb ↦ ⟨ha.1.mul hb.1, ha.2.mul hb.2⟩
  inv_mem' := fun ha ↦ ⟨ha.1.inv, ha.2.inv⟩

/-- The elements of `lineGroupFull H` whose support is bounded above: a version of `D_{*H}` on the
extended line with a condition at `-∞`. -/
def lineGroupBoundedAbove (H : Subgroup NNRealˣ) : Subgroup LineAut where
  carrier := {a | IsLocallyRightHLinearLine H a ∧ AffNearBotH H a ∧ IdNearTop a}
  one_mem' := ⟨IsLocallyRightHLinearLine.one H, AffNearBotH.one H, IdNearTop.one⟩
  mul_mem' := fun ha hb ↦ ⟨ha.1.mul hb.1, ha.2.1.mul hb.2.1, ha.2.2.mul hb.2.2⟩
  inv_mem' := fun ha ↦ ⟨ha.1.inv, ha.2.1.inv, ha.2.2.inv⟩

lemma isDlabLikeAff_of_line {H : Subgroup NNRealˣ} {a : LineAut}
    (ha : IsLocallyRightHLinearLine H a) (hb : AffNearBot a) : IsDlabLikeAff a := by
  refine ⟨hb, fun p _ ↦ ?_⟩
  obtain ⟨ε, hε, h, hh⟩ := ha p
  refine ⟨ε, hε, Dlab.slopeToReal h.1, fun x hx₁ hx₂ ↦ ?_⟩
  rcases hx₁.lt_or_eq with hx₁ | rfl
  · exact hh x hx₁ hx₂
  · ring

section Injective

variable [S : SlopeChoice]

/-- **Interval form, arbitrary embeddings.** -/
theorem not_induced_interval_injective (H : Subgroup NNRealˣ) (A : Subgroup Dlab.IntervalAut)
    (hA : ∀ f ∈ A, Dlab.IsLocallyRightHLinear H f) (e : DlabGroup S.K →* A)
    (he : Function.Injective e) (u : A) : ∃ f, e (αo f) ≠ u⁻¹ * e f * u := by
  set E : DlabGroup S.K →* LineAut := extHom.comp (A.subtype.comp e) with hEdef
  have hE : Function.Injective E := extHom_injective.comp (Subtype.val_injective.comp he)
  have hE_dlab : ∀ g, IsDlabLikeAff (E g) := fun g ↦ (isDlabLike_extHom (hA _ (e g).2)).toAff
  obtain ⟨f, hf⟩ := not_induced_injective_line E hE hE_dlab (extHom u)
    (isDlabLike_extHom (hA _ u.2)).toAff
  refine ⟨f, fun h ↦ hf ?_⟩
  simp only [hEdef, MonoidHom.comp_apply, Subgroup.coe_subtype, h, map_mul, map_inv]

/-- **Line form, arbitrary embeddings.** The bigger group may consist of any locally right
`H`-linear order automorphisms of `ℝ` that are affine near `-∞` (this covers all four Dlab groups
`D_H`, `D_{H*}`, `D_{*H}`, `\bar D_H` on the extended line). -/
theorem not_induced_line_injective (H : Subgroup NNRealˣ) (A : Subgroup LineAut)
    (hA : ∀ a ∈ A, IsLocallyRightHLinearLine H a ∧ AffNearBot a) (e : DlabGroup S.K →* A)
    (he : Function.Injective e) (u : A) : ∃ f, e (αo f) ≠ u⁻¹ * e f * u := by
  set E : DlabGroup S.K →* LineAut := A.subtype.comp e with hEdef
  have hE : Function.Injective E := Subtype.val_injective.comp he
  have hE_dlab : ∀ g, IsDlabLikeAff (E g) := fun g ↦
    isDlabLikeAff_of_line (hA _ (e g).2).1 (hA _ (e g).2).2
  obtain ⟨f, hf⟩ := not_induced_injective_line E hE hE_dlab u
    (isDlabLikeAff_of_line (hA _ u.2).1 (hA _ u.2).2)
  refine ⟨f, fun h ↦ hf ?_⟩
  simp only [hEdef, MonoidHom.comp_apply, Subgroup.coe_subtype, h, Subgroup.coe_mul,
    Subgroup.coe_inv]

end Injective

/-- **Kourovka Notebook Problem 21.149, strongest form.** For every nontrivial slope group `K`
there is an order automorphism of the Dlab group `D_K([0,1])` (with Dlab's order) which is not
induced by conjugation by an element of any bigger Dlab group, for any embedding of `D_K([0,1])`
into the bigger group and for any slope group `H` of the bigger group. -/
theorem kourovka_21_149_injective (K : Subgroup NNRealˣ) (hK : K ≠ ⊥) :
    ∃ α : DlabGroup K ≃*o DlabGroup K,
      (∀ (H : Subgroup NNRealˣ) (A : Subgroup Dlab.IntervalAut),
        (∀ f ∈ A, Dlab.IsLocallyRightHLinear H f) →
        ∀ e : DlabGroup K →* A, Function.Injective e →
        ∀ u : A, ∃ f, e (α f) ≠ u⁻¹ * e f * u) ∧
      (∀ (H : Subgroup NNRealˣ) (A : Subgroup LineAut),
        (∀ a ∈ A, IsLocallyRightHLinearLine H a ∧ AffNearBot a) →
        ∀ e : DlabGroup K →* A, Function.Injective e →
        ∀ u : A, ∃ f, e (α f) ≠ u⁻¹ * e f * u) := by
  obtain ⟨S, rfl⟩ := SlopeChoice.exists_of_ne_bot hK
  exact ⟨@αo S, @not_induced_interval_injective S, @not_induced_line_injective S⟩

/-- The case `K = ⟨2⟩` (the group of Gong–Yang–Zeng). -/
theorem kourovka_21_149_injective_two :
    ∃ α : DlabGroup W ≃*o DlabGroup W,
      (∀ (H : Subgroup NNRealˣ) (A : Subgroup Dlab.IntervalAut),
        (∀ f ∈ A, Dlab.IsLocallyRightHLinear H f) →
        ∀ e : DlabGroup W →* A, Function.Injective e →
        ∀ u : A, ∃ f, e (α f) ≠ u⁻¹ * e f * u) ∧
      (∀ (H : Subgroup NNRealˣ) (A : Subgroup LineAut),
        (∀ a ∈ A, IsLocallyRightHLinearLine H a ∧ AffNearBot a) →
        ∀ e : DlabGroup W →* A, Function.Injective e →
        ∀ u : A, ∃ f, e (α f) ≠ u⁻¹ * e f * u) :=
  kourovka_21_149_injective W W_ne_bot

/-- The six Dlab groups of Gong–Yang–Zeng (four on `[0,1]`, and `D_H`, `D_{H*}` on the extended
line) and the two groups `lineGroupBoundedAbove H`, `lineGroupFull H` satisfy the hypotheses of
`kourovka_21_149_injective`, for every slope subgroup `H`. -/
theorem families_satisfy_hypotheses (H : Subgroup NNRealˣ) :
    (∀ f ∈ Dlab.subgroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ f ∈ leftIntervalGroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ f ∈ rightIntervalGroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ f ∈ fullIntervalGroup H, Dlab.IsLocallyRightHLinear H f) ∧
    (∀ a ∈ lineGroupBounded H, IsLocallyRightHLinearLine H a ∧ AffNearBot a) ∧
    (∀ a ∈ lineGroupBoundedBelow H, IsLocallyRightHLinearLine H a ∧ AffNearBot a) ∧
    (∀ a ∈ lineGroupBoundedAbove H, IsLocallyRightHLinearLine H a ∧ AffNearBot a) ∧
    (∀ a ∈ lineGroupFull H, IsLocallyRightHLinearLine H a ∧ AffNearBot a) :=
  ⟨fun _ hf ↦ hf.1, fun _ hf ↦ hf.1, fun _ hf ↦ hf.1, fun _ hf ↦ hf,
    fun _ ha ↦ ⟨ha.1, ha.2.1.affNearBot⟩, fun _ ha ↦ ⟨ha.1, ha.2.affNearBot⟩,
    fun _ ha ↦ ⟨ha.1, ha.2.1.affNearBot⟩, fun _ ha ↦ ⟨ha.1, ha.2.affNearBot⟩⟩

end Kourovka21149

end

/- ## Section: `Sanity` -/

section

/-
# Sanity checks for the formal statements

* `αo_induced_by_h`: `αo` *is* induced by conjugation with `h` in the group of all order
  automorphisms of `ℝ`. The main theorems are therefore not vacuous: the hypothesis that the
  conjugating element lies in a Dlab group is essential.
* `not_isDlabLikeAff_h`: `h` is not Dlab-like; its support components accumulate at `0`.
* `extHom_mem_lineGroupBounded`: the standard embedding of `D_K([0,1])` into the line group
  `D_K` (bounded support on the extended line) exists. Together with
  `inclusion_orderPreserving` for the interval groups, this shows that the quantifier over
  embeddings `e` in the main theorems is not empty.
-/

open Set Filter

namespace Kourovka21149

open LineAut

section Witness

variable [S : SlopeChoice]

/-- `αo` is induced by conjugation with `h` among all order automorphisms of `ℝ`. -/
theorem αo_induced_by_h (f : DlabGroup S.K) :
    extHom (αo f).1 = (extHom hAut)⁻¹ * extHom f.1 * extHom hAut :=
  ι_α f

/-- The conjugating homeomorphism `h` is not Dlab-like: it lies in no Dlab group. -/
theorem not_isDlabLikeAff_h : ¬ IsDlabLikeAff (extHom hAut) := by
  intro hd
  refine no_staircase_aff hd X (fun m ↦ (X (m + 1) + X m) / 2) (fun m ↦ ?_) (fun m ↦ ?_)
    (fun m ↦ ?_) (fun m ↦ ?_)
  · rw [extHom_hAut, hF_X]
  · rw [extHom_hAut]
    exact (lt_hF (m := m) (by linarith [X_succ_lt m]) (by linarith [X_succ_lt m])).ne'
  · linarith [X_succ_lt m]
  · linarith [X_succ_lt m]

end Witness

/-- The extension of a locally right `H`-linear interval automorphism is locally right
`H`-linear on `ℝ`. -/
lemma isLocallyRightHLinearLine_extHom {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut}
    (hf : Dlab.IsLocallyRightHLinear H f) : IsLocallyRightHLinearLine H (extHom f) := by
  intro p
  rcases lt_or_ge p 0 with hp | hp
  · refine ⟨-p, by linarith, 1, fun x hx1 hx2 ↦ ?_⟩
    rw [extHom_apply_of_nonpos f (by linarith), extHom_apply_of_nonpos f hp]
    simp [Dlab.slopeToReal]
  rcases lt_or_ge p 1 with hp1 | hp1
  · obtain ⟨ε, hε, h, hh⟩ :=
      hf ⟨p, hp, hp1.le⟩ (show (⟨p, hp, hp1.le⟩ : unitInterval) < 1 from hp1)
    refine ⟨min ε (1 - p), lt_min hε (by linarith), h, fun x hx1 hx2 ↦ ?_⟩
    have hx1' : x < 1 := by linarith [min_le_right ε (1 - p)]
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hx1'.le⟩
    have := hh (x := ⟨x, hxI⟩) hx1 (by linarith [min_le_left ε (1 - p)])
    rw [extHom_apply_coe f ⟨x, hxI⟩ |>.symm] at this
    rw [show extHom f p = ((f ⟨p, hp, hp1.le⟩ : unitInterval) : ℝ) from
      extHom_apply_coe f ⟨p, hp, hp1.le⟩]
    exact this
  · refine ⟨1, one_pos, 1, fun x hx1 _ ↦ ?_⟩
    rw [extHom_apply_of_one_le f (by linarith), extHom_apply_of_one_le f hp1]
    simp [Dlab.slopeToReal]

/-- The standard embedding of `D_H([0,1])` into the line group `D_H`. -/
lemma extHom_mem_lineGroupBounded {H : Subgroup NNRealˣ} {f : Dlab.IntervalAut}
    (hf : f ∈ Dlab.subgroup H) : extHom f ∈ lineGroupBounded H :=
  ⟨isLocallyRightHLinearLine_extHom hf.1, idNearBot_extHom f,
    ⟨1, fun _ hx ↦ extHom_apply_of_one_le f hx⟩⟩

/-- An injective homomorphism from `D_K([0,1])` into the line group `D_K` exists. -/
theorem exists_embedding_lineGroupBounded (K : Subgroup NNRealˣ) :
    ∃ e : DlabGroup K →* lineGroupBounded K, Function.Injective e := by
  refine ⟨(extHom.comp (Dlab.subgroup K).subtype).codRestrict (lineGroupBounded K)
    fun f ↦ extHom_mem_lineGroupBounded f.2, fun f g h ↦ ?_⟩
  have h' := congrArg Subtype.val h
  exact Subtype.val_injective (extHom_injective h')

end Kourovka21149

end

/- ## Section: `FCTarget` -/

section FCTarget

open Filter Topology Set
open scoped unitInterval

namespace Kourovka.«21.149»

/- ### The statement definitions agree with the ones of the development -/

lemma isLocallyRightLinear_iff {H : Subgroup NNRealˣ} {f : ℝ ≃o ℝ} :
    IsLocallyRightLinear H f ↔ Kourovka21149.IsLocallyRightHLinearLine H f := by
  constructor
  · intro h a
    obtain ⟨ε, hε, k, hk, hh⟩ := h a
    exact ⟨ε, hε, ⟨k, hk⟩, hh⟩
  · intro h a
    obtain ⟨ε, hε, k, hh⟩ := h a
    exact ⟨ε, hε, k.1, k.2, hh⟩

lemma eventually_atBot_iff_idNearBot {f : ℝ ≃o ℝ} :
    (∀ᶠ x in atBot, f x = x) ↔ Kourovka21149.IdNearBot f :=
  Filter.eventually_atBot

lemma eventually_atTop_iff_idNearTop {f : ℝ ≃o ℝ} :
    (∀ᶠ x in atTop, f x = x) ↔ Kourovka21149.IdNearTop f :=
  Filter.eventually_atTop

lemma dlabLt_iff_fdlt {G : Subgroup (ℝ ≃o ℝ)} {f g : G} :
    DlabLt f g ↔ Kourovka21149.FDLt f g := Iff.rfl

/- ### Order automorphisms of `I` inside those of `ℝ` -/

/-- The extension of an order automorphism of `I` by the identity fixes every point outside
`(0, 1)`. -/
lemma extHom_eq_of_not_mem_Ioo (g : Dlab.IntervalAut) {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 1) :
    Kourovka21149.extHom g x = x := by
  rcases lt_or_ge x 0 with h0 | h0
  · exact Kourovka21149.extHom_apply_of_nonpos g h0
  rcases lt_or_ge x 1 with h1 | h1
  · obtain rfl : x = 0 := le_antisymm (not_lt.1 fun h ↦ hx ⟨h, h1⟩) h0
    have h := Kourovka21149.extHom_apply_coe g 0
    rw [show g 0 = 0 from g.map_bot] at h
    simpa using h
  · exact Kourovka21149.extHom_apply_of_one_le g h1

/-- An order automorphism of `ℝ` that fixes every point outside `(0, 1)` restricts to an order
automorphism of `I`. -/
noncomputable def restrictI (f : ℝ ≃o ℝ) (hf : ∀ x ∉ Ioo (0 : ℝ) 1, f x = x) :
    Dlab.IntervalAut where
  toEquiv := f.toEquiv.subtypeEquiv fun x ↦ by
    have h0 : f 0 = 0 := hf 0 fun h ↦ lt_irrefl _ h.1
    have h1 : f 1 = 1 := hf 1 fun h ↦ lt_irrefl _ h.2
    change x ∈ Icc (0 : ℝ) 1 ↔ f x ∈ Icc (0 : ℝ) 1
    constructor
    · rintro ⟨hx0, hx1⟩
      exact ⟨h0.symm.le.trans (f.monotone hx0), (f.monotone hx1).trans h1.le⟩
    · rintro ⟨hx0, hx1⟩
      exact ⟨f.le_iff_le.1 (h0.le.trans hx0), f.le_iff_le.1 (hx1.trans h1.symm.le)⟩
  map_rel_iff' {a b} := by
    change f a ≤ f b ↔ (a : ℝ) ≤ b
    exact f.le_iff_le

lemma extHom_restrictI (f : ℝ ≃o ℝ) (hf : ∀ x ∉ Ioo (0 : ℝ) 1, f x = x) :
    Kourovka21149.extHom (restrictI f hf) = f := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact Kourovka21149.extHom_apply_coe (restrictI f hf) ⟨x, hx⟩
  · rw [Kourovka21149.extHom_apply_of_not_mem _ hx, hf x fun h ↦ hx (Ioo_subset_Icc_self h)]

/-- If the extension of `g` is locally right `H`-linear on `ℝ`, then `g` is locally right
`H`-linear on `I`. -/
lemma isLocallyRightHLinear_of_extHom {H : Subgroup NNRealˣ} {g : Dlab.IntervalAut}
    (h : Kourovka21149.IsLocallyRightHLinearLine H (Kourovka21149.extHom g)) :
    Dlab.IsLocallyRightHLinear H g := by
  intro a _
  obtain ⟨ε, hε, k, hk⟩ := h a
  refine ⟨ε, hε, k, fun x hx₁ hx₂ ↦ ?_⟩
  have := hk x hx₁ hx₂
  rwa [Kourovka21149.extHom_apply_coe, Kourovka21149.extHom_apply_coe] at this

/-- The extension of `g` is the identity near `0` in `ℝ` iff `g` is the identity near `0` in
`I`. -/
lemma eventually_extHom_zero_iff (g : Dlab.IntervalAut) :
    (∀ᶠ x in 𝓝 (0 : ℝ), Kourovka21149.extHom g x = x) ↔ Dlab.IsIdentityNearZero g := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
    refine Kourovka21149.isIdentityNearZero_of hδ fun x hx ↦ Subtype.ext ?_
    have h' := hball (y := (x : ℝ)) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg x.2.1])
    rwa [Kourovka21149.extHom_apply_coe] at h'
  · intro h
    obtain ⟨δ, hδ, hid⟩ := Kourovka21149.exists_id_near_zero h
    filter_upwards [Iio_mem_nhds hδ] with x hx
    rcases lt_or_ge x 0 with h0 | h0
    · exact Kourovka21149.extHom_apply_of_nonpos g h0
    rcases lt_or_ge x 1 with h1 | h1
    · have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨h0, h1.le⟩
      have h' := Kourovka21149.extHom_apply_coe g ⟨x, hxI⟩
      rw [hid ⟨x, hxI⟩ hx] at h'
      exact h'
    · exact Kourovka21149.extHom_apply_of_one_le g h1

/-- The extension of `g` is the identity near `1` in `ℝ` iff `g` is the identity near `1` in
`I`. -/
lemma eventually_extHom_one_iff (g : Dlab.IntervalAut) :
    (∀ᶠ x in 𝓝 (1 : ℝ), Kourovka21149.extHom g x = x) ↔ Dlab.IsIdentityNearOne g := by
  constructor
  · intro h
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
    refine Kourovka21149.isIdentityNearOne_of (δ := 1 - δ) (by linarith) fun x hx ↦
      Subtype.ext ?_
    have h' := hball (y := (x : ℝ)) (by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [x.2.2])]
      linarith)
    rwa [Kourovka21149.extHom_apply_coe] at h'
  · intro h
    obtain ⟨δ, hδ, hid⟩ := Kourovka21149.exists_id_near_one h
    filter_upwards [Ioi_mem_nhds hδ] with x hx
    rcases lt_or_ge x 1 with h1 | h1
    · rcases lt_or_ge x 0 with h0 | h0
      · exact Kourovka21149.extHom_apply_of_nonpos g h0
      · have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨h0, h1.le⟩
        have h' := Kourovka21149.extHom_apply_coe g ⟨x, hxI⟩
        rw [hid ⟨x, hxI⟩ hx] at h'
        exact h'
    · exact Kourovka21149.extHom_apply_of_one_le g h1

/-- A group of locally right `H`-linear order automorphisms of `I` with an end condition `P`,
seen inside the order automorphisms of `ℝ`. -/
lemma mem_map_extHom_iff {H : Subgroup NNRealˣ} {A : Subgroup Dlab.IntervalAut}
    {P : Dlab.IntervalAut → Prop} {Q : (ℝ ≃o ℝ) → Prop}
    (hA : ∀ g, g ∈ A ↔ Dlab.IsLocallyRightHLinear H g ∧ P g)
    (hPQ : ∀ g, P g ↔ Q (Kourovka21149.extHom g)) (f : ℝ ≃o ℝ) :
    f ∈ A.map Kourovka21149.extHom ↔
      IsLocallyRightLinear H f ∧ (∀ x ∉ Ioo (0 : ℝ) 1, f x = x) ∧ Q f := by
  rw [Subgroup.mem_map, isLocallyRightLinear_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hl, hp⟩ := (hA g).1 hg
    exact ⟨Kourovka21149.isLocallyRightHLinearLine_extHom hl,
      fun x hx ↦ extHom_eq_of_not_mem_Ioo g hx, (hPQ g).1 hp⟩
  · rintro ⟨hl, hout, hq⟩
    refine ⟨restrictI f hout, (hA _).2 ⟨isLocallyRightHLinear_of_extHom ?_, (hPQ _).2 ?_⟩,
      extHom_restrictI f hout⟩
    · rwa [extHom_restrictI]
    · rwa [extHom_restrictI]

/-- Every Dlab group consists of locally right `H`-linear order automorphisms of `ℝ` that are the
identity near `-∞`. -/
lemma IsDlabGroup.isLocallyRightHLinearLine {H : Subgroup NNRealˣ} {A : Subgroup (ℝ ≃o ℝ)}
    (hA : IsDlabGroup H A) :
    ∀ a ∈ A, Kourovka21149.IsLocallyRightHLinearLine H a ∧ Kourovka21149.AffNearBot a := by
  intro a ha
  have hI : (∀ x ∉ Ioo (0 : ℝ) 1, a x = x) → Kourovka21149.AffNearBot a := fun h ↦
    Kourovka21149.IdNearBot.affNearBot ⟨-1, fun x hx ↦ h x fun hx' ↦ by linarith [hx'.1]⟩
  rcases hA with h | h | h | h | h | h
  · obtain ⟨h₁, h₂, -⟩ := (h a).1 ha
    exact ⟨isLocallyRightLinear_iff.1 h₁, hI h₂⟩
  · obtain ⟨h₁, h₂, -⟩ := (h a).1 ha
    exact ⟨isLocallyRightLinear_iff.1 h₁, hI h₂⟩
  · obtain ⟨h₁, h₂, -⟩ := (h a).1 ha
    exact ⟨isLocallyRightLinear_iff.1 h₁, hI h₂⟩
  · obtain ⟨h₁, h₂⟩ := (h a).1 ha
    exact ⟨isLocallyRightLinear_iff.1 h₁, hI h₂⟩
  · obtain ⟨h₁, h₂, -⟩ := (h a).1 ha
    exact ⟨isLocallyRightLinear_iff.1 h₁, (eventually_atBot_iff_idNearBot.1 h₂).affNearBot⟩
  · obtain ⟨h₁, h₂⟩ := (h a).1 ha
    exact ⟨isLocallyRightLinear_iff.1 h₁, (eventually_atBot_iff_idNearBot.1 h₂).affNearBot⟩

/- ### Sanity checks: the six Dlab groups exist, and embeddings exist -/

/-- `D_H(I)`, seen inside the order automorphisms of `ℝ`. -/
lemma isDlabGroup_interval (H : Subgroup NNRealˣ) :
    IsDlabGroup H ((Dlab.subgroup H).map Kourovka21149.extHom) :=
  Or.inl fun f ↦ mem_map_extHom_iff
    (P := fun g ↦ Dlab.IsIdentityNearZero g ∧ Dlab.IsIdentityNearOne g)
    (Q := fun f ↦ (∀ᶠ x in 𝓝 (0 : ℝ), f x = x) ∧ ∀ᶠ x in 𝓝 (1 : ℝ), f x = x)
    (fun _ ↦ Iff.rfl)
    (fun g ↦ (and_congr (eventually_extHom_zero_iff g) (eventually_extHom_one_iff g)).symm) f

/-- `D_{H*}(I)`, seen inside the order automorphisms of `ℝ`. -/
lemma isDlabGroup_left (H : Subgroup NNRealˣ) :
    IsDlabGroup H ((Kourovka21149.leftIntervalGroup H).map Kourovka21149.extHom) :=
  Or.inr <| Or.inl fun f ↦ mem_map_extHom_iff (P := Dlab.IsIdentityNearZero)
    (Q := fun f ↦ ∀ᶠ x in 𝓝 (0 : ℝ), f x = x) (fun _ ↦ Iff.rfl)
    (fun g ↦ (eventually_extHom_zero_iff g).symm) f

/-- `D_{*H}(I)`, seen inside the order automorphisms of `ℝ`. -/
lemma isDlabGroup_right (H : Subgroup NNRealˣ) :
    IsDlabGroup H ((Kourovka21149.rightIntervalGroup H).map Kourovka21149.extHom) :=
  Or.inr <| Or.inr <| Or.inl fun f ↦ mem_map_extHom_iff (P := Dlab.IsIdentityNearOne)
    (Q := fun f ↦ ∀ᶠ x in 𝓝 (1 : ℝ), f x = x) (fun _ ↦ Iff.rfl)
    (fun g ↦ (eventually_extHom_one_iff g).symm) f

/-- `\bar D_H(I)`, seen inside the order automorphisms of `ℝ`. -/
lemma isDlabGroup_full (H : Subgroup NNRealˣ) :
    IsDlabGroup H ((Kourovka21149.fullIntervalGroup H).map Kourovka21149.extHom) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl fun f ↦ by
    simpa only [and_true] using mem_map_extHom_iff (P := fun _ ↦ True) (Q := fun _ ↦ True)
      (fun _ ↦ ⟨fun h ↦ ⟨h, trivial⟩, fun h ↦ h.1⟩) (fun _ ↦ Iff.rfl) f

/-- `D_H` on the extended real line. -/
lemma isDlabGroup_bounded (H : Subgroup NNRealˣ) :
    IsDlabGroup H (Kourovka21149.lineGroupBounded H) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl fun f ↦ by
    rw [isLocallyRightLinear_iff, eventually_atBot_iff_idNearBot,
      eventually_atTop_iff_idNearTop]
    rfl

/-- `D_{H*}` on the extended real line. -/
lemma isDlabGroup_boundedBelow (H : Subgroup NNRealˣ) :
    IsDlabGroup H (Kourovka21149.lineGroupBoundedBelow H) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr fun f ↦ by
    rw [isLocallyRightLinear_iff, eventually_atBot_iff_idNearBot]; rfl

/-- The hypotheses on the embedding `e` can be met: `D_K(I)` embeds into every bigger interval
group `\bar D_H(I)` and into the line group `D_K`. -/
lemma exists_embeddings (K H : Subgroup NNRealˣ) (hKH : K ≤ H) :
    (∃ e : Dlab.subgroup K →* Kourovka21149.fullIntervalGroup H, Function.Injective e) ∧
      ∃ e : Dlab.subgroup K →* Kourovka21149.lineGroupBounded K, Function.Injective e :=
  ⟨⟨Subgroup.inclusion (fun _ hf ↦ hf.1.mono hKH), Subgroup.inclusion_injective _⟩,
    Kourovka21149.exists_embedding_lineGroupBounded K⟩

/- ### The target -/

/-- `D_K(I)` and its copy inside the order automorphisms of `ℝ`. -/
noncomputable def extEquiv (K : Subgroup NNRealˣ) :
    DlabGroup K ≃* (Dlab.subgroup K).map Kourovka21149.extHom :=
  (Dlab.subgroup K).equivMapOfInjective Kourovka21149.extHom Kourovka21149.extHom_injective

lemma coe_extEquiv (K : Subgroup NNRealˣ) (f : DlabGroup K) :
    ((extEquiv K f : (Dlab.subgroup K).map Kourovka21149.extHom) : ℝ ≃o ℝ) =
      Kourovka21149.extHom f.1 :=
  Subgroup.coe_equivMapOfInjective_apply _ _ _ _

/-- Dlab's order on the copy of `D_K(I)` is Dlab's order on `D_K(I)`. -/
lemma dlabLt_extEquiv {K : Subgroup NNRealˣ} (f g : DlabGroup K) :
    DlabLt (extEquiv K f) (extEquiv K g) ↔ f < g := by
  rw [dlabLt_iff_fdlt, coe_extEquiv, coe_extEquiv, Kourovka21149.lt_iff_intervalFDLt,
    Kourovka21149.intervalFDLt_iff]

/-- The witness: `G = D_⟨2⟩(I)`, extended to `ℝ` by the identity, with the automorphism
`f ↦ h⁻¹ f h`. It preserves Dlab's order and is not induced by conjugation in any Dlab group. -/
lemma exists_witness :
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧
          ∃ e : G →* A, Function.Injective e ∧ ∃ u : A, ∀ f : G, e (α f) = u⁻¹ * e f * u := by
  let S : Kourovka21149.SlopeChoice := Kourovka21149.SlopeChoice.two
  refine ⟨S.K, (Dlab.subgroup S.K).map Kourovka21149.extHom, isDlabGroup_interval S.K,
    (extEquiv S.K).symm.trans (Kourovka21149.αo.toMulEquiv.trans (extEquiv S.K)),
    fun f g ↦ ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := (extEquiv S.K).surjective f
    obtain ⟨b, rfl⟩ := (extEquiv S.K).surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [dlabLt_extEquiv, dlabLt_extEquiv]
    exact Kourovka21149.α_lt_iff a b
  · rintro ⟨H, A, hA, e, he, u, hu⟩
    obtain ⟨f, hf⟩ := Kourovka21149.not_induced_line_injective H A
      hA.isLocallyRightHLinearLine (e.comp (extEquiv S.K).toMonoidHom)
      (he.comp (extEquiv S.K).injective) u
    apply hf
    have h := hu (extEquiv S.K f)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
    exact h

/-- The Formal Conjectures-style statement of `../FClikeLean/21_149.lean`, with the answer
`True`. The witness is `G = D_⟨2⟩(I)`, extended to `ℝ` by the identity, with the automorphism
`αo f = h⁻¹ f h`. The statement for every nontrivial slope group `K` is
`Kourovka21149.kourovka_21_149_injective`. -/
theorem kourovka_21_149 : answer(True) ↔
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ (H : Subgroup NNRealˣ) (A : Subgroup (ℝ ≃o ℝ)), IsDlabGroup H A ∧
          ∃ e : G →* A, Function.Injective e ∧ ∃ u : A, ∀ f : G, e (α f) = u⁻¹ * e f * u := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ trivial⟩
  exact exists_witness

/-- The original form of the problem, from the main statement: an inner automorphism is induced
by conjugation in the Dlab group `A = G` itself. -/
theorem kourovka_21_149.variants.not_inner : answer(True) ↔
    ∃ (K : Subgroup NNRealˣ) (G : Subgroup (ℝ ≃o ℝ)), IsDlabGroup K G ∧
      ∃ α : G ≃* G, (∀ f g : G, DlabLt (α f) (α g) ↔ DlabLt f g) ∧
        ¬ ∃ u : G, ∀ f : G, α f = u⁻¹ * f * u := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ trivial⟩
  obtain ⟨K, G, hG, α, hα, hn⟩ := kourovka_21_149.1 trivial
  exact ⟨K, G, hG, α, hα, fun ⟨u, hu⟩ ↦
    hn ⟨K, G, hG, MonoidHom.id G, Function.injective_id, u, hu⟩⟩

end Kourovka.«21.149»

#print axioms Kourovka.«21.149».kourovka_21_149
#print axioms Kourovka.«21.149».kourovka_21_149.variants.not_inner
#print axioms Kourovka21149.kourovka_21_149_injective

end FCTarget
