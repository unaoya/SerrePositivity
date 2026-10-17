module
public import SerrePositivity.DifferentialGraded.Derived.LeftUnitOuterRestriction
public import Mathlib.Data.ZMod.Basic

/-! # 外側制限と単位子：標数2と独立宇宙での検査 -/
@[expose] public section
noncomputable section
universe v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

-- Fは任意。全導来後因子Qについて、両出力圏の局所Hom条件を明示する。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
    (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
    (F : DGFunctor (ZMod 2) D C)
    (hC : localHomKFlat (ZMod 2) C) (hD : localHomKFlat (ZMod 2) D)
    (Q : DerivedBimoduleCategory (ZMod 2) B C) :
    (leftUnitOuterLeftRestrictionComparison (ZMod 2) B C D F hC hD).app Q =
      (derivedBimoduleLeftUnitIso (ZMod 2) B D hD).hom.app
        ((derivedBimoduleRestriction (ZMod 2) B D B C (DGFunctor.id B) F).obj Q) := by
  rw [leftUnitOuterLeftRestrictionComparison_eq]
  rfl

-- 通常右単位squareは局所Hom条件・Hom準同型性を要求しない。
example (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (F : DGFunctor (ZMod 2) D B) (P : BimoduleCategory (ZMod 2) B C) :
    (composeRightRestrictionIso (ZMod 2) B D C C F P
        (BimoduleCategory.of (ZMod 2) C C (Bimodule.diagonal (ZMod 2) C))).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) B D C F).map
        (rightBimoduleUnitIso (ZMod 2) B C
          (BimoduleCategory.underlying (ZMod 2) B C P)).hom =
    (rightBimoduleUnitIso (ZMod 2) D C
      (Bimodule.rightRestriction (ZMod 2) B D C F
        (BimoduleCategory.underlying (ZMod 2) B C P))).hom :=
  rightBimoduleUnitIso_rightRestriction (ZMod 2) B D C F P

#print axioms leftUnitValue_leftRestriction
#print axioms leftBimoduleUnitIso_leftRestriction
#print axioms rightUnitValue_rightRestriction
#print axioms rightBimoduleUnitIso_rightRestriction
#print axioms leftUnitOuterLeftRestrictionComparison
#print axioms leftUnitOuterLeftRestrictionComparison_app
#print axioms leftUnitOuterLeftRestrictionComparison_model
#print axioms leftUnitOuterLeftRestrictionComparison_kFlat
#print axioms leftUnitOuterLeftRestrictionComparison_eq
