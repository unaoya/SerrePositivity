module
public import SerrePositivity.DifferentialGraded.Resolution.DiagonalComparison
public import Mathlib.Data.ZMod.Basic

/-! # 対角制限と既存解像度変更の対角保存の検査 -/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section Restriction
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

-- 比較の値はF自身のHom写像であり、条件は本質的全射性を含まない。
example (b d : D) :
    (BimoduleCategory.valueEvaluation A D D b d).map
        (Bimodule.diagonalRestrictionMap A D E F) = F.map b d :=
  Bimodule.diagonalRestrictionMap_value A D E F b d

example : BimoduleCategory.quasiIso A D D (Bimodule.diagonalRestrictionMap A D E F) ↔
    HomQuasiIso F :=
  Bimodule.diagonalRestrictionMap_quasiIso_iff A D E F

-- どちらの圏にも局所Hom K-flat性を追加せず、既存の導来制限上の同型を得る。
example (hF : HomQuasiIso F) :
    (bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj ≅
      (derivedBimoduleRestriction A D D E E F F).obj
        ((bimoduleToDerived A E E).obj (rightKFlatDiagonal A E).obj) :=
  derivedDiagonalRestrictionIso A D E F hF
end Restriction

section Resolutions
open SerrePositivity.DifferentialGraded.ResolutionBimodule
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

-- 元の対象型のsmallnessは比較左脚に不要。
example (P : KFlatDGResolution.{u, v, w} A D) :
    (comparisonLeft A P P).obj (diagonal A P) ≅ comparisonDiagonal A P :=
  comparisonLeftDiagonalIso A P

variable [Small.{u} D]

-- 指定した既存changeEquivalenceを使い、変更前後のsource宇宙は独立。
example (P : KFlatDGResolution.{u, v, w} A D)
    (Q : KFlatDGResolution.{u, v, z} A D) :
    (changeEquivalence A P P Q Q).functor.obj (diagonal A P) ≅ diagonal A Q :=
  changeDiagonalIso A P Q
end Resolutions

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E]
    (F : DGFunctor (ZMod 2) D E) (hF : HomQuasiIso F) :
    IsIso (derivedDiagonalRestrictionMap (ZMod 2) D E F) :=
  derivedDiagonalRestrictionMap_isIso (ZMod 2) D E F hF

#print axioms Bimodule.diagonalRestriction_leftAt_map
#print axioms Bimodule.diagonalRestriction_value_left_naturality
#print axioms Bimodule.diagonalRestrictionMap
#print axioms Bimodule.diagonalRestrictionMap_value
#print axioms Bimodule.diagonalRestrictionMap_quasiIso_iff
#print axioms derivedDiagonalRestrictionMap
#print axioms derivedDiagonalRestrictionIso
#print axioms derivedDiagonalRestrictionIso_hom
#print axioms derivedDiagonalRestrictionMap_isIso
#print axioms ResolutionBimodule.comparisonDiagonal
#print axioms ResolutionBimodule.comparisonLeftDiagonalIso
#print axioms ResolutionBimodule.comparisonRightDiagonalIso
#print axioms ResolutionBimodule.canonicalComparisonDiagonalIso
#print axioms ResolutionBimodule.changeDiagonalIso
