module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourBottomPath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGlueContourRefinement

/-!
概要：元の G・S′R と W を保つ貼合せ比較に、既存 affineViaB を実際に代入する。
方針：T′(LW) の結合則と T′L の全射同定により、元の二重経路の右辺だけを移す。
規約：指定経路 W や左辺を定数扱いしない。使われ方：元の Γ の右逆三角形への接続。
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

lemma postnikovCommonRightGlueViaBRight_hom :
    (postnikovCommonRightGlueContourRefinedRight R f c d hj).hom =
      (postnikovCommonRightViaBThenBottom R f c d hj).hom := by
  let t := postnikovCommonRightContourTargetPath R f c d hj
  let l := postnikovCommonRightContourLeftPath R f c d hj
  let w := postnikovCommonRightContourBottomPath R f c d hj
  let e := postnikovCommonRightToClassifying R f c d
  have ha := congrArg (fun k => e ≫ k)
    (SquareZero.RelativeWitness.comp_assoc_hom t l w).symm
  have hp := SquareZero.RelativeWitness.precomp_comp_hom (t.comp l) w e
  have ht : ((t.comp l).precomp e).hom =
      (postnikovCommonRightViaBContourPath R f c d hj).hom :=
    postnikovCommonRightContourTargetLeft_hom R f c d hj
  have hw : (w.precomp e).hom =
      (postnikovCommonRightContourBottomRefinedPath R f c d hj).hom := rfl
  exact ha.trans (hp.trans (SquareZero.RelativeWitness.comp_congr_hom_of_paths ht hw))

/-- 元の G(S′R) と affineViaB⋅W を、全底射影と両端を固定して結ぶ実二重経路。 -/
def postnikovCommonRightGlueViaBSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueContourRefinedLeft R f c d hj)
    (postnikovCommonRightViaBThenBottom R f c d hj) :=
  SquareZero.RelativeWitnessSquare.replacePaths
    (postnikovCommonRightGlueContourRefinedSquare R f c d hj) rfl
    (postnikovCommonRightGlueViaBRight_hom R f c d hj)

def postnikovCommonRightGlueViaBTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightGlueContourRefinedLeft R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R f c d hj)
      (postnikovCommonRightViaBThenBottom R f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightGlueViaBSquare R f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
