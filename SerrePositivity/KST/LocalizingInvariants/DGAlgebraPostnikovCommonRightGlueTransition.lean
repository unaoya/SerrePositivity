module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingEdges
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGlueTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)
  {a b : postnikovCommonRightCellSource R f c d ⟶ postnikovZeroClassTarget R (B.obj i).obj 1 1}
  (v : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) a b)

/-- 同じ右経路を零底上の B 遷移で写す。 -/
def postnikovCommonRightTransitionRelative : SquareZero.RelativeWitness
    ((postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d) ≫
      postnikovMap R (B.transition hj).hom 0)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (a ≫ postnikovZeroClassMap R 1 1 (B.transition hj).hom)
    (b ≫ postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightTransitionRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (a := a) (b := b) (v := v)

/-- 同じ元の P と、classifying 正方形の各次数全射準同型細分へそろえる。 -/
def postnikovCommonRightTransitionOverRelative : SquareZero.RelativeWitness
    (postnikovCommonRightClassifyingProjection R f c d ≫
      postnikovCommonRightClassifyingBase R f c d hj)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (a ≫ postnikovZeroClassMap R 1 1 (B.transition hj).hom))
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (b ≫ postnikovZeroClassMap R 1 1 (B.transition hj).hom)) :=
  PostnikovCommonCore.postnikovCommonRightTransitionOverRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (a := a) (b := b) (v := v)

lemma postnikovCommonRightTransitionOverRelative_hom :
    (postnikovCommonRightTransitionOverRelative R f c d hj v).hom =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫ v.hom ≫
      Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightTransitionOverRelative_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (a := a) (b := b) (v := v)

lemma postnikovCommonRightAffineFixedGlue_transition_linear :
    (postnikovCommonRightTransitionOverRelative R f c d hj
      (postnikovCommonRightAffineFixedGlue R f c d)).hom.hom =
    (((postnikovCommonRightTransitionOverRelative R f c d hj
      (postnikovCommonRightFixedTargetRelative R f c d)).comp
      (postnikovCommonRightTransitionOverRelative R f c d hj
        (postnikovCommonRightFixedCentralRelative R f c d))).comp
      (postnikovCommonRightTransitionOverRelative R f c d hj
        (postnikovCommonRightFixedSourceRelative R f c d)).reverse).hom.hom :=
  PostnikovCommonCore.postnikovCommonRightAffineFixedGlue_transition_linear
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
