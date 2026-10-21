module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTensorInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputUnliftedPrecomp
/-!
概要：同じ二入力 Hom の固定入力制限を、元の共変・反変 D(R) 値 Hom へ全関手同型で比較する。
方針：同じ実分解の指定逆と augmentation を保ち、元の関手・値に照合する。
規約：始域は tensor dg 圏の nerve。元の直積上の二変数関手との比較は別工程。
使われ方：二変数導来 Hom の実出力分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ実 Hom ∞ 関手の固定入力制限の全関手比較。 -/
def dgSemifreeDerivedHomTensor_sourceIso (Q : SemifreeDGModules R D) :
    FunctorIso
      (dgNerve.map (dgTensorIncludeFirst R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) Q) ≫
        dgSemifreeDerivedHomTensorInfinity R D)
      (dgSemifreeDerivedHomSourceDGopInfinity R D Q) := by
  have e := dgModuleOutputResolution_unliftedPrecompIso.{u, v, 0} R
    (SemifreeDGModules R D)ᵒᵖ
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D)) PUnit.{1}
    (dgTensorIncludeFirst R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) Q)
    (dgSemifreeHomTensorModuleDG R D)
  rw [dgSemifreeHomTensorModuleDG_first] at e
  simpa only [dgSemifreeDerivedHomTensorInfinity, dgSemifreeDerivedHomSourceDGopInfinity,
    Category.assoc] using! e.symm
/-- 同じ実 Hom ∞ 関手の固定入力制限の全関手比較。 -/
def dgSemifreeDerivedHomTensor_targetIso (P : SemifreeDGModules R D) :
    FunctorIso
      (dgNerve.map (dgTensorIncludeSecond R (SemifreeDGModules R D)ᵒᵖ
        (SemifreeDGModules R D) (op P)) ≫ dgSemifreeDerivedHomTensorInfinity R D)
      (dgSemifreeDerivedHomTargetInfinity R D P) := by
  have e := dgModuleOutputResolution_unliftedPrecompIso.{u, v, 0} R
    (SemifreeDGModules R D)
    (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D)) PUnit.{1}
    (dgTensorIncludeSecond R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D) (op P))
    (dgSemifreeHomTensorModuleDG R D)
  rw [dgSemifreeHomTensorModuleDG_second] at e
  simpa only [dgSemifreeDerivedHomTensorInfinity, dgSemifreeDerivedHomTargetInfinity,
    Category.assoc] using! e.symm
end SerrePositivity.InfinityCategories
