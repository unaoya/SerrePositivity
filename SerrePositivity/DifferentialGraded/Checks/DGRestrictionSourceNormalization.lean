module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionSource
public import Mathlib.Data.ZMod.Basic

/-! # 外側・中間sourceの正規化と左単位モデル経路の検査 -/
@[expose] public section
noncomputable section
universe v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

-- 任意の関手F、終端Cだけの局所Hom K-flat条件、標数2でも同じ指定モデルの経路を使う。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (F : DGFunctor (ZMod 2) D B) (hC : localHomKFlat (ZMod 2) C)
    (Q : RightKFlatBimoduleCategory (ZMod 2) B C)
    (R : RightKFlatBimoduleCategory (ZMod 2) D C) (q : _) (hq : _) :
    leftUnitRestrictionModelPath (ZMod 2) B D C F hC Q R q hq =
      (leftUnitRestrictionModelSourceIso (ZMod 2) B D C F hC Q R q hq).hom ≫
        (derivedBimoduleLeftUnitIso (ZMod 2) D C hC).hom.app
          ((derivedBimoduleRestriction (ZMod 2) D C B C F (DGFunctor.id C)).obj
            ((bimoduleToDerived (ZMod 2) B C).obj Q.obj)) :=
  leftUnitRestrictionModelPath_eq_sourceLeftUnit (ZMod 2) B D C F hC Q R q hq

#check restrictedMiddleSourcePrefix_normalize
#check restrictedMiddleSourcePrefix_model
#check leftUnitRestrictionModelPath_eq
#check leftUnitRestrictionModelSourceIso_leftUnit

#print axioms restrictedMiddleSourcePrefix
#print axioms restrictedMiddleSourcePrefix_normalize
#print axioms restrictedMiddleSourcePrefix_model
#print axioms leftUnitRestrictedModelPrefix
#print axioms leftUnitRestrictionModelPath
#print axioms leftUnitRestrictionModelPath_eq
#print axioms leftUnitRestrictionModelSourceIso
#print axioms leftUnitRestrictionModelSourceIso_leftUnit
#print axioms leftUnitRestrictionModelPath_eq_sourceLeftUnit
