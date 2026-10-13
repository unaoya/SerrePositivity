module

public import SerrePositivity.CLMST.PerfectoidIsogeny
public import SerrePositivity.CommutativeAlgebra.EtaleAwayBaseChange
public import SerrePositivity.CommutativeAlgebra.RegularBaseChange
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # 平坦基底変更した有限代数への isogeny の適用

有限代数 D の g の外でのエタール性と g・p の正則性から、平坦な perfectoid
A 代数 R に対する R⊗_A D の perfectoid 化への単射性と余核の冪による零化を導く。
完備化した根の塔の平坦性そのものを、この適用補題の仮定から証明したとは扱わない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
attribute [local instance] HasDerivedCategory.standard

variable (A R D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing R] [CommRing D] [Algebra A R] [Algebra A D]
    [Module.Finite A D] [Module.Flat A R]

local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- 平坦な perfectoid 基底への有限代数の基底変更に、命題2.4.7を適用する。
主イデアル全体のエタール条件、p 冪ねじれの有界性、g の正則性を個別に供給する。 -/
theorem tensor_injective_and_exists_pow_annihilates_coker
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : A)
    (hg : IsSMulRegular D (algebraMap A D g)) (hp : IsSMulRegular D (p : D))
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    Function.Injective (perfectoidizationModuleMap R (R ⊗[A] D) p hR) ∧
      ∃ N : ℕ, ∀ x : (Perfectoidization R (R ⊗[A] D) p hR) ⧸
        (perfectoidizationModuleMap R (R ⊗[A] D) p hR).range,
        (algebraMap A R g ^ N) • x = 0 := by
  have hregular := isSMulRegular_tensorProduct_of_flat A R D g hg
  have hp' : IsSMulRegular (R ⊗[A] D) (p : R ⊗[A] D) := by
    have hbase := isSMulRegular_tensorProduct_of_flat A R D (p : A) (by simpa using hp)
    change Function.Injective (fun x : R ⊗[A] D ↦ algebraMap A R (p : A) • x) at hbase
    change Function.Injective (fun x : R ⊗[A] D ↦ (p : R ⊗[A] D) * x)
    simpa [Algebra.smul_def] using hbase
  have hbounded := exists_pow_torsion_bound_of_isSMulRegular (R ⊗[A] D) p hp'
  have het : ∀ x ∈ Ideal.span {algebraMap A R g},
      let _ := GenericEtale.awayAlgebra R (R ⊗[A] D) x
      Algebra.Etale (Localization.Away x)
        (Localization.Away (algebraMap R (R ⊗[A] D) x)) := by
    intro x hx
    exact GenericEtale.etale_away_baseChange_of_mem_span_singleton A R D g x hx hEtale
  exact injective_and_exists_pow_annihilates_coker R (R ⊗[A] D) p hR
    (Ideal.span {algebraMap A R g}) (Submodule.fg_span_singleton _) het hbounded
    (algebraMap A R g) (Ideal.subset_span (Set.mem_singleton _)) hregular

end SerrePositivity.CLMST
