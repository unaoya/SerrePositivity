module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourSourceRight
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueViaBComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroTransportCompositeHomotopy

/-!
概要：元の G と分子・分母の二自然性合成を、指定 W を保つ実二重経路で結ぶ。
方針：元の左境界 S′R の全射同定を、既存の貼合せ比較へ代入する。
規約：元の Γ 源・射影・両端・G・W を保持。使われ方：実 roof の右三角形への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightGlueRefinedPath :=
  ((postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightAffineFixedGlue R f c d)).precomp
    (postnikovCommonRightToClassifying R f c d)).rebase
    (postnikovCommonRightToClassifying_projection R f c d)

def postnikovCommonRightDenContourPath :=
  (postnikovCommonRightContourSourceRightRefined R f c d hj).replaceHom
    (postnikovCommonRightDenZeroComposite R f c d hj).hom
    (postnikovCommonRightContourSourceRight_hom R f c d hj)

def postnikovCommonRightGlueThenDen :=
  (postnikovCommonRightGlueRefinedPath R f c d hj).comp
    (postnikovCommonRightDenContourPath R f c d hj)

lemma postnikovCommonRightGlueThenDen_hom :
    (postnikovCommonRightGlueContourRefinedLeft R f c d hj).hom =
      (postnikovCommonRightGlueThenDen R f c d hj).hom := by
  let g := postnikovCommonRightTransitionLift R f c d hj
    (postnikovCommonRightAffineFixedGlue R f c d)
  let sr := postnikovCommonRightContourSourceRight R f c d hj
  let e := postnikovCommonRightToClassifying R f c d
  have hg : (g.precomp e).hom = (postnikovCommonRightGlueRefinedPath R f c d hj).hom := rfl
  have hd : (sr.precomp e).hom = (postnikovCommonRightDenContourPath R f c d hj).hom :=
    postnikovCommonRightContourSourceRight_hom R f c d hj
  exact (SquareZero.RelativeWitness.precomp_comp_hom g sr e).trans
    (SquareZero.RelativeWitness.comp_congr_hom_of_paths hg hd)

/-- 元の G⋅分母自然性と分子自然性⋅W を同じ Γ 射影上で結ぶ実二重経路。 -/
def postnikovCommonRightGlueNaturalitySquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueThenDen R f c d hj)
    (postnikovCommonRightViaBThenBottom R f c d hj) :=
  SquareZero.RelativeWitnessSquare.replacePaths (postnikovCommonRightGlueViaBSquare R f c d hj)
    (postnikovCommonRightGlueThenDen_hom R f c d hj) rfl

def postnikovCommonRightGlueNaturalityTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueThenDen R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightViaBThenBottom R f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightGlueNaturalitySquare R f c d hj)

/-- 同じ四つの実模型射の合成を結ぶ経路。class 経路の輸送だけに留めない。 -/
def postnikovCommonRightGlueNaturalityCompositeHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueRefinedPath R f c d hj) ≫
    SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightDenContourPath R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightViaBContourPath R f c d hj) ≫
    SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightContourBottomRefinedPath R f c d hj)) := by
  let z := SquareZeroExtension.transportCompositeHomotopy
    (postnikovCommonRightClassifyingLayer R f c d hj)
    (postnikovCommonRightGlueRefinedPath R f c d hj)
    (postnikovCommonRightDenContourPath R f c d hj)
    (postnikovCommonRightViaBContourPath R f c d hj)
    (postnikovCommonRightContourBottomRefinedPath R f c d hj)
    (postnikovCommonRightGlueNaturalitySquare R f c d hj)
  exact z

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
