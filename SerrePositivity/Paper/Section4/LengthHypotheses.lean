module

public import SerrePositivity.Paper.Section4.KoszulInputs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# §4 の仮定 (4.1) からの有限性

## 目的

正の冪についての Koszul 消滅と商の長さの公式から、既存の有限版比較が要求する
全ての自然数冪での有限性を供給する。§2の環や長さ関数の構成は使わない。

## 零乗の扱い

パラメータの個数が正なら、零乗の列には単位元が含まれる。
その Koszul 複体は単位元に台をもつため、ホモロジーは零となる。
これにより (4.1) の正の冪という範囲を、余分な有限性仮定を加えずに補う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory Limits
open scoped ENNReal

/-- 単位元を含む定数列の Koszul ホモロジーは零。
Koszul 複体の台の定理から、恒等写像の零ホモトピーをホモロジーへ移す。 -/
lemma koszul_ones_homology_isZero {C : Type u} [CommRing C]
    {e : ℕ} (he : 0 < e) (i : ℤ) :
    IsZero ((koszulComplex (fun _ : Fin e ↦ (1 : C))).homology i) := by
  obtain ⟨v, hv⟩ := isSupported_koszulComplex (fun _ : Fin e ↦ (1 : C))
  obtain ⟨H⟩ := hv ⟨0, he⟩
  have h := H.homologyMap_eq i
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  simp only [one_pow, one_smul] at h
  exact (IsZero.iff_id_eq_zero _).mpr h

/-- 仮定 (4.1) は全ての自然数冪の Koszul ホモロジーの長さの有限性を含意する。
正の冪では高次の消滅と第零商の有限性、零乗では単位元による消滅を使う。 -/
lemma koszul_finite_of_section4
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {J : Ideal C} (lam : NormalizedLength C J) {e : ℕ} (z : Fin e → A) (he : 0 < e)
    (r : ℕ)
    (hzero : ∀ v : ℕ, 0 < v → ∀ j : ℕ, 0 < j →
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun k ↦ algebraMap A C (z k ^ v))) =
        ((v ^ e * r : ℕ) : ℝ≥0∞)) :
    ∀ v j : ℕ,
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤ := by
  intro v j
  by_cases hv : 0 < v
  · exact normalized_koszul_finite lam _ (hzero v hv)
      (by rw [hquot v hv]; exact ENNReal.natCast_ne_top _) (-(j : ℤ))
  · have hv0 : v = 0 := by omega
    subst v
    have hx : (fun k : Fin e ↦ algebraMap A C (z k ^ 0)) = (fun _ ↦ (1 : C)) := by
      funext k
      simp
    rw [hx]
    let := ModuleCat.subsingleton_of_isZero (koszul_ones_homology_isZero (C := C) he (-(j : ℤ)))
    rw [lam.len_eq_zero_of_subsingleton]
    exact ENNReal.zero_ne_top

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
