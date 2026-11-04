module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.ReducedModel
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# 被約 noetherian 基底での一般点からの延長

## 概要
有限モデルの三つの分母を一つにそろえ、有限エタール・普遍同相分解を得る。

## 方針
分母の積を取り、エタール locus の開性、nil 性の移送、主局所化の全射性を使う。

## 規約
選ぶ分母は基底の非零因子なので、全極小点を残す。

## 使われ方
一般の noetherian 基底では、両環の被約化に適用する。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 分母を増やしても、局所化されたイデアルの nil 性は保たれる。 -/
theorem ideal_map_away_le_nilradical_of_dvd
    {A : Type u} [CommRing A] (I : Ideal A) {a b : A} (hab : a ∣ b)
    (h : I.map (algebraMap A (Localization.Away a)) ≤ nilradical (Localization.Away a)) :
    I.map (algebraMap A (Localization.Away b)) ≤ nilradical (Localization.Away b) := by
  have hu : IsUnit (algebraMap A (Localization.Away b) a) :=
    isUnit_of_dvd_unit (map_dvd _ hab) (IsLocalization.Away.algebraMap_isUnit b)
  let f : Localization.Away a →+* Localization.Away b := IsLocalization.Away.lift a hu
  rw [Ideal.map_le_iff_le_comap] at h ⊢
  intro x hx
  have hn := (mem_nilradical.mp (h hx)).map f
  apply mem_nilradical.mpr
  simpa only [f, IsLocalization.Away.lift_eq] using hn

/-- 分母を増やしても、主局所化のエタール性は保たれる。 -/
theorem etale_away_of_dvd {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] {a b : A} (hab : a ∣ b)
    (h : Algebra.Etale R (Localization.Away a)) :
    Algebra.Etale R (Localization.Away b) := by
  obtain ⟨c, rfl⟩ := hab
  exact Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
    ((PrimeSpectrum.basicOpen_mul_le_left a c).trans
      (Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr h))

/-- 被約な有限代数の一般点での分解は、一つの主開集合へ延びる。 -/
theorem exists_reduced_spread_out
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsReduced R] [IsReduced S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hZp : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    ∃ g : nonZeroDivisors R, HasEtaleFactorization p
      (Localization.awayMap (algebraMap R S) g) := by
  obtain ⟨T, hfinite, ⟨g₁, h₁⟩, ⟨g₂, h₂⟩, ⟨g₃, h₃⟩⟩ :=
    exists_reduced_generic_model R S p hZp
  let : Module.Finite R T := hfinite
  let : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  let : Module.Finite T S := Module.Finite.of_restrictScalars_finite R T S
  let : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let g : nonZeroDivisors R := g₁ * g₂ * g₃
  have hg₁ : (g₁ : R) ∣ g := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hg₂ : (g₂ : R) ∣ g := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hg₃ : (g₃ : R) ∣ g := dvd_mul_left _ _
  let R' := Localization.Away (g : R)
  let T' := Localization.Away (algebraMap R T g)
  let S' := Localization.Away (algebraMap R S g)
  let a : R' →+* T' := Localization.awayMap (algebraMap R T) g
  let b : T' →+* S' := Localization.awayMap T.val.toRingHom (algebraMap R T g)
  let : Algebra R' T' := a.toAlgebra
  let : IsScalarTower R R' T' := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.map_eq _ _ _ x).symm
  let : Module.Finite R' T' := Module.Finite.of_isLocalizedModule
    (Submonoid.powers (g : R)) (IsScalarTower.toAlgHom R T T').toLinearMap
  let : Algebra.Etale R T' := etale_away_of_dvd (map_dvd (algebraMap R T) hg₁) h₁
  let : IsNoetherianRing R' := IsLocalization.isNoetherianRing (Submonoid.powers (g : R)) R'
  let : Algebra.FinitePresentation R' T' :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FormallyEtale R' T' :=
    Algebra.FormallyEtale.localization_base (Submonoid.powers (g : R))
  let : Algebra.Etale R' T' := ⟨inferInstance, inferInstance⟩
  refine ⟨g, CommRingCat.of T', a, b, ?_, inferInstance, inferInstance, ?_, ?_⟩
  · apply IsLocalization.ringHom_ext (Submonoid.powers (g : R))
    ext x
    simp only [RingHom.comp_apply, a, b, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  · apply isUniversalHomeomorphism_away_of_nil_diagonal Subtype.val_injective
      (algebraMap R T g)
    have hn := ideal_map_away_le_nilradical_of_dvd _
      (map_dvd (algebraMap R (S ⊗[T] S)) hg₂) h₂
    have he : algebraMap T (S ⊗[T] S) (algebraMap R T g) =
        algebraMap R (S ⊗[T] S) g :=
      (IsScalarTower.algebraMap_apply R T (S ⊗[T] S) g).symm
    simpa only [he] using hn
  · apply invertPrimeMap_awayMap_bijective p T.val.toRingHom (algebraMap R T g)
      Subtype.val_injective
    exact Localization.awayMap_surjective_of_dvd T.val.toRingHom
      (mul_dvd_mul_right (map_dvd (algebraMap R T) hg₃) (p : T)) h₃

end SerrePositivity.CommutativeAlgebra
