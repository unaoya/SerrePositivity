module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCentralTransition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeBaseChangeComposition
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareCongr

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

def postnikovCommonRightTransitionLift :
    let z := postnikovCommonRightTransitionOverRelative R hn f c d hj v
    SquareZero.RelativeWitness (postnikovCommonRightClassifyingProjection R hn f c d)
      (bimoduleRestrict (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1))
      (SquareZero.baseChangeLift (postnikovCommonRightClassifyingBase R hn f c d hj) _ _ _
        z.source_projection)
      (SquareZero.baseChangeLift (postnikovCommonRightClassifyingBase R hn f c d hj) _ _ _
        z.target_projection) :=
  SquareZero.baseChangeRelativeWitness (postnikovCommonRightClassifyingBase R hn f c d hj) _ _
    (postnikovCommonRightTransitionOverRelative R hn f c d hj v)

lemma postnikovCommonRightTransitionLift_map :
    (postnikovCommonRightTransitionLift R hn f c d hj v).hom ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R hn f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R hn f c d) ≫ v.hom ≫
      Path.map R (postnikovZeroClassMap R n 1 (B.transition hj).hom) := by
  change (SquareZero.baseChangeRelativeWitness _ _ _
    (postnikovCommonRightTransitionOverRelative R hn f c d hj v)).hom ≫ _ = _
  rw [SquareZero.baseChangeRelativeWitness_map, postnikovCommonRightTransitionOverRelative_hom]

lemma postnikovCommonRightAffineFixedGlue_transitionLift_hom :
    (postnikovCommonRightTransitionLift R hn f c d hj
      (postnikovCommonRightAffineFixedGlue R hn f c d)).hom =
    (((postnikovCommonRightTransitionLift R hn f c d hj
      (postnikovCommonRightFixedTargetRelative R hn f c d)).comp
      (postnikovCommonRightTransitionLift R hn f c d hj
        (postnikovCommonRightFixedCentralRelative R hn f c d))).comp
      (postnikovCommonRightTransitionLift R hn f c d hj
        (postnikovCommonRightFixedSourceRelative R hn f c d)).reverse).hom := by
  let q := postnikovCommonRightClassifyingBase R hn f c d hj
  let N := DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj n) 1
  let p := postnikovCommonRightClassifyingProjection R hn f c d
  let T := postnikovCommonRightTransitionOverRelative R hn f c d hj
    (postnikovCommonRightFixedTargetRelative R hn f c d)
  let V := postnikovCommonRightTransitionOverRelative R hn f c d hj
    (postnikovCommonRightFixedCentralRelative R hn f c d)
  let S := postnikovCommonRightTransitionOverRelative R hn f c d hj
    (postnikovCommonRightFixedSourceRelative R hn f c d)
  let G := postnikovCommonRightTransitionOverRelative R hn f c d hj
    (postnikovCommonRightAffineFixedGlue R hn f c d)
  have hg : G.hom = ((T.comp V).comp S.reverse).hom :=
    Mon.Hom.ext (postnikovCommonRightAffineFixedGlue_transition_linear R hn f c d hj)
  change (SquareZero.baseChangeRelativeWitness q N p G).hom = _
  calc
    _ = (SquareZero.baseChangeRelativeWitness q N p ((T.comp V).comp S.reverse)).hom :=
      SquareZero.baseChangeRelativeWitness_congr_hom q N p _ _ hg
    _ = ((SquareZero.baseChangeRelativeWitness q N p (T.comp V)).comp
        (SquareZero.baseChangeRelativeWitness q N p S.reverse)).hom :=
      SquareZero.baseChangeRelativeWitness_comp_hom q N p _ _
    _ = _ := SquareZero.RelativeWitness.comp_congr_hom
      (SquareZero.baseChangeRelativeWitness_comp_hom q N p T V)
      (SquareZero.baseChangeRelativeWitness_reverse_hom q N p S)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
