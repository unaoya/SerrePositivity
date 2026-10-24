module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightContourBottomPath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueContourRefinement

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonRightGlueViaBRight_hom :
    (postnikovCommonRightGlueContourRefinedRight R hn f c d hj).hom =
      (postnikovCommonRightViaBThenBottom R hn f c d hj).hom := by
  let t := postnikovCommonRightContourTargetPath R hn f c d hj
  let l := postnikovCommonRightContourLeftPath R hn f c d hj
  let w := postnikovCommonRightContourBottomPath R hn f c d hj
  let e := postnikovCommonRightToClassifying R hn f c d
  have ha := congrArg (fun k => e ≫ k)
    (SquareZero.RelativeWitness.comp_assoc_hom t l w).symm
  have hp := SquareZero.RelativeWitness.precomp_comp_hom (t.comp l) w e
  have ht : ((t.comp l).precomp e).hom =
      (postnikovCommonRightViaBContourPath R hn f c d hj).hom :=
    postnikovCommonRightContourTargetLeft_hom R hn f c d hj
  have hw : (w.precomp e).hom =
      (postnikovCommonRightContourBottomRefinedPath R hn f c d hj).hom := rfl
  exact ha.trans (hp.trans (SquareZero.RelativeWitness.comp_congr_hom_of_paths ht hw))

/-- 元の G(S′R) と affineViaB⋅W を、全底射影と両端を固定して結ぶ実二重経路。 -/
def postnikovCommonRightGlueViaBSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightGlueContourRefinedLeft R hn f c d hj)
    (postnikovCommonRightViaBThenBottom R hn f c d hj) :=
  SquareZero.RelativeWitnessSquare.replacePaths
    (postnikovCommonRightGlueContourRefinedSquare R hn f c d hj) rfl
    (postnikovCommonRightGlueViaBRight_hom R hn f c d hj)

def postnikovCommonRightGlueViaBTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R hn f c d hj)
      (postnikovCommonRightGlueContourRefinedLeft R hn f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightClassifyingLayer R hn f c d hj)
      (postnikovCommonRightViaBThenBottom R hn f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightGlueViaBSquare R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
