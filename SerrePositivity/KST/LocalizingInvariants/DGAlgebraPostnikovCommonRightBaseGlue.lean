module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCentralTransition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeBaseChangeComposition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareCongr

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightBaseGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：B 遷移後の元の貼合せと、P 上へ持ち上げた三経路の貼合せが全経路として一致する。
方針：同じ指定底での合成・反転の厳密な保存を使う。
規約：新しい中央経路へ取り替えない。使われ方：元の Γ の右合成への輪郭比較。
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
  {a b : postnikovCommonRightCellSource R f c d ⟶ postnikovZeroClassTarget R (B.obj i).obj 1 1}
  (v : SquareZero.RelativeWitness
    (postnikovCommonRightCellProjection R f c d ≫ postnikovCommonRightZeroBase R f c d)
    (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj i).obj 1) 1) a b)

def postnikovCommonRightTransitionLift :
    let z := postnikovCommonRightTransitionOverRelative R f c d hj v
    SquareZero.RelativeWitness (postnikovCommonRightClassifyingProjection R f c d)
      (bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))
      (SquareZero.baseChangeLift (postnikovCommonRightClassifyingBase R f c d hj) _ _ _
        z.source_projection)
      (SquareZero.baseChangeLift (postnikovCommonRightClassifyingBase R f c d hj) _ _ _
        z.target_projection) :=
  PostnikovCommonCore.postnikovCommonRightTransitionLift
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (a := a) (b := b) (v := v)

lemma postnikovCommonRightTransitionLift_map :
    (postnikovCommonRightTransitionLift R f c d hj v).hom ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫ v.hom ≫
      Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightTransitionLift_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (a := a) (b := b) (v := v)

lemma postnikovCommonRightAffineFixedGlue_transitionLift_hom :
    (postnikovCommonRightTransitionLift R f c d hj
      (postnikovCommonRightAffineFixedGlue R f c d)).hom =
    (((postnikovCommonRightTransitionLift R f c d hj
      (postnikovCommonRightFixedTargetRelative R f c d)).comp
      (postnikovCommonRightTransitionLift R f c d hj
        (postnikovCommonRightFixedCentralRelative R f c d))).comp
      (postnikovCommonRightTransitionLift R f c d hj
        (postnikovCommonRightFixedSourceRelative R f c d)).reverse).hom :=
  PostnikovCommonCore.postnikovCommonRightAffineFixedGlue_transitionLift_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
