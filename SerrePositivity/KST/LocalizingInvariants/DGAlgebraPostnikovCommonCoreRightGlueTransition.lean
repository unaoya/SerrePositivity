module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingEdges
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

/-!
概要：元の三経路と貼合せを B 遷移で移し、元の P の同じ cell 細分上へそろえる。
方針：基底つき相対経路の移送と、零底射の厳密因子化を使う。
規約：全経路の実 affine 式を保持。使われ方：classifying 輪郭比較と三経路の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)
  {a b : postnikovCommonRightCellSource R hn f c d ⟶ postnikovZeroClassTarget R (B.obj i).obj n 1}
  (v : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj n) 1) a b)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

/-- 同じ右経路を零底上の B 遷移で写す。 -/
def postnikovCommonRightTransitionRelative : SquareZero.RelativeWitness
    ((postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightZeroBase R hn f c d) ≫
      postnikovMap R (B.transition hj).hom 0)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (a ≫ postnikovZeroClassMap R n 1 (B.transition hj).hom)
    (b ≫ postnikovZeroClassMap R n 1 (B.transition hj).hom) :=
  v.mapOver (postnikovMap R (B.transition hj).hom 0)
    (postnikovZeroClassMap R n 1 (B.transition hj).hom)
    (postnikovZeroClassMap_projection R n 1 (B.transition hj).hom)

/-- 同じ元の P と、classifying 正方形の各次数全射準同型細分へそろえる。 -/
def postnikovCommonRightTransitionOverRelative : SquareZero.RelativeWitness
    (postnikovCommonRightClassifyingProjection R hn f c d ≫
      postnikovCommonRightClassifyingBase R hn f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)
    (cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      (a ≫ postnikovZeroClassMap R n 1 (B.transition hj).hom))
    (cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫
      (b ≫ postnikovZeroClassMap R n 1 (B.transition hj).hom)) :=
  ((postnikovCommonRightTransitionRelative R hn f c d hj v).precomp
    (cellAugmentation R (postnikovCommonRightCellSource R hn f c d))).rebase (by
      simp only [postnikovCommonRightClassifyingProjection,
        postnikovCommonRightClassifyingBase_zero, Category.assoc])

lemma postnikovCommonRightTransitionOverRelative_hom :
    (postnikovCommonRightTransitionOverRelative R hn f c d hj v).hom =
    cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫ v.hom ≫
      Path.map R (postnikovZeroClassMap R n 1 (B.transition hj).hom) := rfl

lemma postnikovCommonRightAffineFixedGlue_transition_linear :
    (postnikovCommonRightTransitionOverRelative R hn f c d hj
      (postnikovCommonRightAffineFixedGlue R hn f c d)).hom.hom =
    (((postnikovCommonRightTransitionOverRelative R hn f c d hj
      (postnikovCommonRightFixedTargetRelative R hn f c d)).comp
      (postnikovCommonRightTransitionOverRelative R hn f c d hj
        (postnikovCommonRightFixedCentralRelative R hn f c d))).comp
      (postnikovCommonRightTransitionOverRelative R hn f c d hj
        (postnikovCommonRightFixedSourceRelative R hn f c d)).reverse).hom.hom := by
  rw [postnikovCommonRightTransitionOverRelative_hom]
  simp only [SquareZero.RelativeWitness.comp_hom_linear,
    SquareZero.RelativeWitness.reverse_hom_linear,
    postnikovCommonRightTransitionOverRelative_hom]
  rw [Mon.comp_hom', Mon.comp_hom', postnikovCommonRightAffineFixedGlue_linear]
  have hd := congrArg Mon.Hom.hom (Path.diagonal_naturality R
    (postnikovZeroClassMap R n 1 (B.transition hj).hom))
  simp only [Mon.comp_hom'] at hd
  dsimp only [postnikovZeroClassTarget] at hd
  simp only [Mon.comp_hom', comp_add, comp_sub, add_comp, sub_comp, Category.assoc, hd]
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
