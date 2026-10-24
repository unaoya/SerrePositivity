module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightSourceFirstComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageZeroMap

/-!
概要：元の輪郭の R と第二 ImageWitness の零底像を、同じ Γ 源上で取り出す。
方針：既存の classifying 正方形の内側 target 評価と、元の係数同型を使う。
規約：源の細分射を選び直さない。使われ方：S′R の全経路同定。
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

def postnikovCommonRightContourRightPath := SquareZero.RectangleOfHom.innerTarget
  (postnikovCommonRightClassifyingLayer R hn f c d hj)
  (postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj)
  (postnikovCommonRightClassifyingProjection R hn f c d)
  (postnikovCommonRightClassifyingBaseChangeHom_projection R hn f c d hj)

def postnikovCommonRightContourRightRefinedPath :=
  ((postnikovCommonRightContourRightPath R hn f c d hj).precomp
    (postnikovCommonRightToClassifying R hn f c d)).rebase
    (postnikovCommonRightToClassifying_projection R hn f c d)

def postnikovCommonRightDenSecondZeroPath :=
  (((postnikovCellImageRelative R (B.obj i).obj (B.obj j).obj
    (postnikovCommonClassBase R hn f c d) n hn
    ((roofRefine R hn f c d.zero.source_le).roof.denominator ≫
      postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom n)
      (B.transition hj).hom).mapOver (𝟙 _)
    (postnikovCommonRightDenCompositeZeroIso R hn f c d hj).hom
    ((postnikovCommonRightDenCompositeZeroIso_projection R hn f c d hj).trans
      (Category.comp_id _).symm)).precomp
    (postnikovCommonRightImageToSecond R hn f c d)).rebase
    (q' := postnikovCommonClassStandardGlueProjection R hn f c d) (by
      rw [Category.comp_id]
      exact postnikovCommonRightImageToSecond_projection R hn f c d)

lemma postnikovCommonRightContourRightPath_map :
    (postnikovCommonRightContourRightPath R hn f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R hn f c d) ≫
      (postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (postnikovCommonRightDenBase R hn f c d) (B.transition hj).hom).hom ≫
      Path.map R (postnikovClassToZeroBase R (B.obj j).obj n hn 1) := by
  change (postnikovCommonRightClassifyingBaseChangeHom R hn f c d hj ≫
    Path.map R (Path.target R _)) ≫ Path.map R _ = _
  rw [Category.assoc, ← Path.map_comp, ← Path.map_target, Path.map_comp,
    ← Category.assoc, postnikovCommonRightClassifyingBaseChangeHom_map R hn f c d hj,
    postnikovCommonRightClassifyingZeroSquare_target_trace R hn f c d hj]
  simp only [Path.Witness.precompNonpositiveCell, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
