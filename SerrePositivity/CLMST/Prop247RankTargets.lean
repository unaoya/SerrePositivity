module

public import SerrePositivity.CLMST.Prop247RankBaseChange
public import SerrePositivity.CLMST.Prop247QuotientPerfectoidization
public import SerrePositivity.CommutativeAlgebra.PerfectoidTorsionFrobenius

/-! # Prop 2.4.7：原典の rank 像の実 perfectoid 化対象

既存 B3 と B4 を使い、Ri の有限表示性・完備性を仮定せず実対象を供給する。
元の R・Ri の作用、全射性、有限性、底変換の定 rank を保持する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 指定した Ri の perfectoid 化は元の R の全射像であり、R 上有限である。 -/
theorem prop247_rankTarget_surjective_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    [IsScalarTower R (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    (hf : IsPerfectoidization p
      (algebraMap (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T)) :
    Function.Surjective (algebraMap R T) ∧ Module.Finite R T := by
  let I := prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
  let q := (prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)).toRingHom
  have hq : Function.Surjective q := prop247_toOpenSectionImage_surjective R _
  have hf' := prop247_surjective_perfectoidization_of_quotient p hR q hq (algebraMap I T) hf
  have hs : Function.Surjective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R I T]
    exact hf'.comp hq
  exact ⟨hs, Module.Finite.of_surjective (Algebra.linearMap R T) hs⟩

/-- 原典の各 Ri の実 perfectoid 化を、元の二つの代数作用・有限性・定 rank とともに供給する。
普遍対象の新しい存在引用は追加せず、既存 B3 と B4 を用いる。 -/
theorem prop247_rankImage_exists_perfectoid_target
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    let I := prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra I T),
      IsScalarTower R I T ∧ IsPerfectoidization p (algebraMap I T) ∧
      Function.Surjective (algebraMap R T) ∧ Module.Finite R T ∧
      ∀ x : PrimeSpectrum.basicOpen (algebraMap R T g),
        prop247_awayRank T (T ⊗[R] S) (algebraMap R T g) x = n := by
  letI := hR.isReduced R p
  let I := prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
  let q := (prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)).toRingHom
  obtain ⟨T, hT, f, hf⟩ :=
    BhattScholze.exists_perfectoidization_of_perfectoid_surjective_quotient hR q
      (prop247_toOpenSectionImage_surjective R _)
  letI := hT
  letI : Algebra I T := f.toAlgebra
  letI : Algebra R T := (f.comp q).toAlgebra
  letI : IsScalarTower R I T := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hs, hfinite⟩ := prop247_rankTarget_surjective_finite R S p hR g hetale n T hf
  refine ⟨T, hT, inferInstance, inferInstance, inferInstance, hf, hs, hfinite, ?_⟩
  intro x
  exact prop247_awayRank_baseChange_over_rankImage R S g hetale n T x

end SerrePositivity.CLMST
