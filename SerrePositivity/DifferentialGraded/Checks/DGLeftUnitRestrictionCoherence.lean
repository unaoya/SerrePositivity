module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitRestrictionCoherence
public import Mathlib.Data.ZMod.Basic

/-! # 全導来左単位経路と制限後の既存左単位子の一致を検査 -/
@[expose] public section
noncomputable section
universe v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

-- Fは任意、局所Hom条件は終端Cだけ。導来対象Qを指定モデルに限定しない。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (F : DGFunctor (ZMod 2) D B) (hC : localHomKFlat (ZMod 2) C)
    (Q : DerivedBimoduleCategory (ZMod 2) B C) :
    (leftUnitRestrictionDerivedComparison (ZMod 2) B D C F hC).app Q =
      (derivedBimoduleLeftUnitIso (ZMod 2) D C hC).hom.app
        ((derivedBimoduleRestriction (ZMod 2) D C B C F (DGFunctor.id C)).obj Q) := by
  rw [leftUnitRestrictionDerivedComparison_eq]
  rfl

#check leftUnitRestrictionDerivedComparison_model
#check leftUnitRestrictionDerivedComparison_kFlat
#check leftUnitRestrictionDerivedComparison_eq

#print axioms leftUnitRestrictionModelSourceIso_diagonal
#print axioms leftUnitRestrictionDerivedPrefix
#print axioms leftUnitRestrictionDerivedPrefix_model
#print axioms leftUnitRestrictionDerivedComparison_model
#print axioms leftUnitRestrictionDerivedComparison_kFlat
#print axioms leftUnitRestrictionDerivedComparison_eq
