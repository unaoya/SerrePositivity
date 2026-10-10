module

public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # スペクトルの全射と長さ公式からの非自明性

有限局所整域上の階数の正値性を用いて、係数環 C の非自明性を確認する。
Koszul 有限性と Euler 数の計算は `LengthAlgebraRealization` の共通入力を使う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory Limits
open scoped ENNReal

/-- 整域上でスペクトルが全射なら、環準同型は単射。
零素イデアルの逆像となる素イデアルに核が含まれることを使う。 -/
lemma algebraMap_injective_of_spectrum_surjective
    (A T : Type u) [CommRing A] [IsDomain A] [CommRing T] [Algebra A T]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T))) :
    Function.Injective (algebraMap A T) := by
  obtain ⟨q, hq⟩ := hsurj ⟨⊥, inferInstance⟩
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply le_antisymm _ bot_le
  intro a ha
  have h : a ∈ (PrimeSpectrum.comap (algebraMap A T) q).asIdeal := by
    change algebraMap A T a ∈ q.asIdeal
    rw [show algebraMap A T a = 0 from ha]
    exact q.asIdeal.zero_mem
  simpa only [hq] using h

/-- 商の長さが階数に等しいなら、§4 の C は非自明。
有限局所整域 T の階数の正値性と、零加群の長さが零であることから従う。 -/
lemma nontrivial_of_section4_quotient
    {A T C : Type u} [CommRing A] [IsDomain A] [CommRing T] [IsDomain T]
    [Algebra A T] [Module.Finite A T] [CommRing C]
    {J : Ideal C} (lam : NormalizedLength C J) (I : Ideal C)
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (hq : lam.len (C ⧸ I) = (Module.finrank A T : ℝ≥0∞)) : Nontrivial C := by
  let : Module.IsTorsionFree A T :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (algebraMap_injective_of_spectrum_surjective A T hsurj)
  have hr : 0 < Module.finrank A T := Module.finrank_pos
  rcases subsingleton_or_nontrivial C with hC | hC
  · have h0 : (Module.finrank A T : ℝ≥0∞) = 0 :=
      hq.symm.trans (lam.len_eq_zero_of_subsingleton _)
    have : Module.finrank A T = 0 := by exact_mod_cast h0
    omega
  · exact hC

end SerrePositivity.Section4
