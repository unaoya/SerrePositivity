module

public import SerrePositivity.BhattScholze.Andre.CompletelyFaithfulPairReduction
public import SerrePositivity.BhattScholze.PrismaticGeneratorPowerModPFaithful
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-!
# André E1・E2：正則主商への完全忠実平坦性の下降

## 概要

基底と代数で正則な d による通常商は、元の (p,d) 完全忠実平坦性から p 完全忠実平坦性を得る。
BS Rem 7.15（著者版 p.62）の最終生成元商への移送。

## 方針

正則主商の導来比較と二元剰余の二段階比較を合成し、同じ剰余 H⁰ の忠実平坦性を戻す。

## 規約

通常商には標準主商代数作用を使う。完備性・Noether 性・prism 構造は不要。

## 使われ方

具体的な完全 δ 化後の生成元商の p 完全忠実平坦性を証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra

/-- 概要：正則主商への二元完全忠実平坦性の下降。
方針：導来主剰余と通常主商を比較し、二段階剰余の離散性と忠実平坦性を移す。
規約：元の標準代数作用とその標準主商作用を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の perfectoid 商の平坦性。 -/
theorem completelyFaithfullyFlat_principal_quotient_of_pair
    {A : Type u} [CommRing A] (p : ℕ) (d : A) (hd : IsSMulRegular A d)
    (S : Type u) [CommRing S] [Algebra A S]
    (hSd : IsSMulRegular S (algebraMap A S d))
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {(p : A), d}) S) :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A ⧸ Ideal.span {d})})
      (S ⧸ Ideal.span {algebraMap A S d}) := by
  let qd := Ideal.Quotient.mk (Ideal.span {d})
  let q := Ideal.Quotient.mk (Ideal.span {(p : A), d})
  let qp := Ideal.Quotient.mk (Ideal.span {(p : A ⧸ Ideal.span {d})})
  let M := ModuleCat.of A S
  let N := ModuleCat.of (A ⧸ Ideal.span {d}) (S ⧸ Ideal.span {algebraMap A S d})
  let X := boundedAboveDerivedSingleFunctor.obj M
  have hMd : IsSMulRegular M d := by
    intro x y hxy
    apply hSd
    simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using hxy
  let ed := boundedAboveDerivedBaseChangeModuleAugmentationIso qd M
      (scalarExtensionTorVanishing_principal_of_regular d hd M hMd) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (principalScalarExtensionAlgebraQuotientEquiv d S).toModuleIso
  have hz (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d})) i).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) := by
    let e := boundedAboveDerivedBaseChangeModuleAugmentationIso q M
      (scalarExtensionTorVanishing_of_completelyFlat _ M hS.1)
    exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (DerivedCategory.Minus.ι.mapIso e))
  have hf : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), d})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), d})) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) := by
    let := scalarExtension_faithfullyFlat_of_completelyFaithfullyFlat _ M hS
    exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars q).obj M)
      ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv
  have hzN (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) i).obj
        ((boundedAboveDerivedBaseChange qp).obj (boundedAboveDerivedSingleFunctor.obj N)).obj) := by
    let HQ (b : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (A ⧸ Ideal.span {(p : A), b})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), b}))).obj X).obj)
    have hq : HQ (d ^ 1) := Eq.mp (congrArg HQ (pow_one d).symm) (hz i hi)
    let HW (b : A) := IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {b}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {b})})) i).obj
      ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ Ideal.span {b})}))).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X)).obj)
    have hw : HW (d ^ 1) := prismaticGeneratorPowerModP_homology_isZero p d 1 X i hq
    have h' : HW d := Eq.mp (congrArg HW (pow_one d)) hw
    exact h'.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso ed))).symm
  have hfN : Module.FaithfullyFlat
      ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})
      ((ModuleCat.extendScalars qp).obj N) := by
    let HQ (b : A) := Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), b})
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ Ideal.span {(p : A), b})) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), b}))).obj X).obj)
    have hq : HQ (d ^ 1) := Eq.mp (congrArg HQ (pow_one d).symm) hf
    let HW (b : A) := Module.FaithfullyFlat
      ((A ⧸ Ideal.span {b}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {b})})
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {b}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {b})})) 0).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {(p : A ⧸ Ideal.span {b})}))).obj
          ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X)).obj)
    have hw : HW (d ^ 1) := prismaticGeneratorPowerModPH0_faithfullyFlat p d 1 X hq
    have h' : HW d := Eq.mp (congrArg HW (pow_one d)) hw
    let : Module.FaithfullyFlat
        ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})
        ((DerivedCategory.homologyFunctor
          (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
          ((boundedAboveDerivedBaseChange qp).obj
            ((boundedAboveDerivedBaseChange qd).obj X)).obj) := h'
    let e := (DerivedCategory.homologyFunctor
      (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange qp).mapIso ed))
    let : Module.FaithfullyFlat
        ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})
        ((DerivedCategory.homologyFunctor
          (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
          ((boundedAboveDerivedBaseChange qp).obj (boundedAboveDerivedSingleFunctor.obj N)).obj) :=
      Module.FaithfullyFlat.of_linearEquiv _
        ((DerivedCategory.homologyFunctor
          (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
          ((boundedAboveDerivedBaseChange qp).obj ((boundedAboveDerivedBaseChange qd).obj X)).obj)
        e.toLinearEquiv.symm
    exact Module.FaithfullyFlat.of_linearEquiv _
      ((DerivedCategory.homologyFunctor
        (ModuleCat ((A ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : A ⧸ Ideal.span {d})})) 0).obj
        ((boundedAboveDerivedBaseChange qp).obj (boundedAboveDerivedSingleFunctor.obj N)).obj)
      ((boundedAboveDerivedBaseChangeModuleH0Iso qp).app N).toLinearEquiv.symm
  have ht : scalarExtensionTorVanishing qp N := by
    apply (derivedModuleBaseChange_negative_homology_vanishes_iff qp N).mp
    intro n hn
    exact (hzN (-(n : ℤ)) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).mapIso
        ((boundedAboveDerivedBaseChangeModuleNatIso qp).app N)).symm
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction _ N ht hfN.1, ?_⟩
  let := hfN
  let e := (quotientScalarExtensionEquiv (Ideal.span {(p : A ⧸ Ideal.span {d})}) N).trans
    (quotientTensorReductionEquiv (Ideal.span {(p : A ⧸ Ideal.span {d})}) N).symm
  exact Module.FaithfullyFlat.of_linearEquiv _ ((ModuleCat.extendScalars qp).obj N) e.symm

end SerrePositivity.BhattScholze.Andre
