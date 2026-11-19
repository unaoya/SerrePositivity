module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Regular.Basic

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 で使う正則単項イデアルの生成元の選択。
方針：生成元を正則元で割った係数のイデアルが単位イデアルになることを使う。
規約：Algebra, Lemma 10.20.1 のうち正則な単項生成元を持つ特殊形に限る。
使われ方：局所環上で単項小行列式イデアルを生成する一つの小行列式を選ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R : Type*} [CommRing R] [IsLocalRing R]

/--
概要：正則単項イデアルを生成する集合には、その正則元の単元倍が含まれる。
方針：各元を正則元で割った係数のイデアルに一が入ることを示し、局所環の極大イデアルを使う。
規約：KST §5、Stacks 080Z, Lemma 15.8.9 と Algebra, Lemma 10.20.1 の正則単項特殊形。
使われ方：純変換の生成元数を減らすピボット小行列式の選択。
-/
theorem exists_unit_multiple_of_span_eq_regular_principal
    (s : Set R) (f : R) (hf : IsRegular f) (hs : Ideal.span s = Ideal.span {f}) :
    ∃ g ∈ s, ∃ u : Rˣ, g = f * (u : R) := by
  classical
  have hdiv : ∀ x : s, ∃ c : R, x.val = f * c := by
    intro x
    have hx : x.val ∈ Ideal.span {f} := hs ▸ Ideal.subset_span x.property
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨c, hc⟩
  choose c hc using hdiv
  let J : Ideal R := Ideal.span (Set.range c)
  have hle : Ideal.span s ≤ Ideal.span {f} * J := by
    apply Ideal.span_le.mpr
    intro x hx
    apply Ideal.mem_span_singleton_mul.mpr
    exact ⟨c ⟨x, hx⟩, Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩, (hc ⟨x, hx⟩).symm⟩
  have hfm : f ∈ Ideal.span {f} * J :=
    hle (hs.symm ▸ Ideal.mem_span_singleton_self f)
  obtain ⟨z, hz, hfz⟩ := Ideal.mem_span_singleton_mul.mp hfm
  have hz1 : z = 1 := hf.left (hfz.trans (mul_one f).symm)
  have h1 : (1 : R) ∈ J := hz1 ▸ hz
  have hu : ∃ x : s, IsUnit (c x) := by
    by_contra h
    have hnon : ∀ x : s, ¬ IsUnit (c x) := by simpa only [not_exists] using h
    have hmax : J ≤ IsLocalRing.maximalIdeal R := by
      apply Ideal.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact hnon i
    exact (hmax h1) isUnit_one
  obtain ⟨x, u, hu⟩ := hu
  exact ⟨x.val, x.property, u, by rw [hc x, hu]⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
