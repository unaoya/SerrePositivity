module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Basic
public import SerrePositivity.LinearAlgebra.IndependentPerturbation

/-! # 非零イデアルの微分の分数体上の生成

Leibniz 則だけを用いる。局所性・Noether 性・有限次元性は不要。
-/

public section
namespace SerrePositivity

/-- 非零イデアル内の元の微分は、分数体上で全ての微分と同じ部分空間を生成する。 -/
theorem span_derivation_ideal_eq_span_range
    {R S L V : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    [IsScalarTower S L V]
    (δ : Derivation R S V) (H : Ideal S) (hH : H ≠ ⊥) :
    Submodule.span L (δ '' (H : Set S)) = Submodule.span L (Set.range δ) := by
  classical
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    have hex : ∃ x ∈ H, x ≠ 0 := by
      by_contra h
      apply hH
      apply le_antisymm ?_ bot_le
      intro x hx
      simpa using (show x = 0 by aesop)
    obtain ⟨x, hx, hx0⟩ := hex
    let N := Submodule.span L (δ '' (H : Set S))
    have hdx : δ x ∈ N := Submodule.subset_span ⟨x, hx, rfl⟩
    have hdbx : δ (b * x) ∈ N :=
      Submodule.subset_span ⟨b * x, H.mul_mem_left b hx, rfl⟩
    have hbdx : b • δ x ∈ N := by
      rw [← algebraMap_smul L b (δ x)]
      exact N.smul_mem _ hdx
    have hxdb : x • δ b ∈ N := by
      have := N.sub_mem hdbx hbdx
      simpa only [δ.leibniz, add_sub_cancel_left] using this
    have hmap : algebraMap S L x ≠ 0 :=
      fun h ↦ hx0 (IsFractionRing.injective S L (by simpa using h))
    have := N.smul_mem (algebraMap S L x)⁻¹ hxdb
    rw [← algebraMap_smul L x (δ b), smul_smul, inv_mul_cancel₀ hmap, one_smul] at this
    exact this

/-- 全微分が生成するなら、任意の非零イデアルの微分も生成する。 -/
theorem span_derivation_ideal_eq_top
    {R S L V : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    [IsScalarTower S L V]
    (δ : Derivation R S V) (H : Ideal S) (hH : H ≠ ⊥)
    (hδ : Submodule.span L (Set.range δ) = ⊤) :
    Submodule.span L (δ '' (H : Set S)) = ⊤ :=
  (span_derivation_ideal_eq_span_range δ H hH).trans hδ

/-- 指定ベクトルを、非零イデアル内の元の微分で摂動して独立にする。
係数体変更に必要な「元の選択」まで、一般線形代数と Leibniz 則から供給する。 -/
theorem exists_linearIndependent_derivation_perturbation
    {R S L V : Type*} [CommRing R] [CommRing S] [IsDomain S] [Field L]
    [Algebra R S] [Algebra S L] [IsFractionRing S L]
    [AddCommGroup V] [Module R V] [Module S V] [Module L V]
    [IsScalarTower S L V] [FiniteDimensional L V]
    (δ : Derivation R S V) (H : Ideal S) (hH : H ≠ ⊥)
    (hδ : Submodule.span L (Set.range δ) = ⊤)
    {n : ℕ} (b : Fin n → V) (hn : n ≤ Module.finrank L V) :
    ∃ m : Fin n → S, (∀ i, m i ∈ H) ∧
      LinearIndependent L (fun i ↦ b i + δ (m i)) := by
  classical
  obtain ⟨w, hw, hind⟩ := exists_linearIndependent_perturbation
    (span_derivation_ideal_eq_top δ H hH hδ) b hn
  have hex (i : Fin n) : ∃ m ∈ H, δ m = w i := by
    rcases hw i with hzero | himage
    · exact ⟨0, H.zero_mem, by simp [← hzero]⟩
    · exact himage
  choose m hm hdm using hex
  refine ⟨m, hm, ?_⟩
  simpa only [hdm] using hind

end SerrePositivity
