module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroWitness

/-!
概要：細分後の係数逆で移した源 class と、元の低い段の標準 class の実相対経路。
方針：零標的で貼り合わせた経路を、元の class 標的へ実底変更で戻す。
規約：元の係数逆・遷移・両 class と次数全射準同型の源射影を保持。使われ方：次の切断逆。
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
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassCompatibilityCoefficient :
    roofShiftedDenominatorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1 ⟶
        postnikovCommonClassTransitionLayer R hn f c d hj :=
  postnikovCommonShiftedCoefficientMap R hn f c d 1 ≫
    postnikovCommonClassTransitionCoefficient R hn f c d hj

def postnikovCommonClassCompatibilityToCell : postnikovCommonClassStandardGlueSource R hn f c d ⟶
    cellResolution R (postnikovCommonClassBase R hn f c d) :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    postnikovCommonRightGlueToCell R hn f c d

lemma postnikovCommonClassCompatibilityToCell_projection :
    postnikovCommonClassCompatibilityToCell R hn f c d ≫
      cellAugmentation R (postnikovCommonClassBase R hn f c d) =
        postnikovCommonClassStandardGlueProjection R hn f c d := by
  rw [postnikovCommonClassCompatibilityToCell, Category.assoc,
    postnikovCommonRightGlueToCell_projection]
  rfl

lemma postnikovCommonClassStandardGlueLeft_eq :
    postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj) =
      postnikovCommonClassCompatibilityToCell R hn f c d ≫
        postnikovCellClassOver R (B.obj d.zero.stage).obj (postnikovCommonClassBase R hn f c d)
          n hn (roofRefine R hn f c d.zero.source_le).roof.denominator ≫
            SquareZero.coefficientMap (postnikovCommonClassBase R hn f c d)
              (postnikovCommonClassCompatibilityCoefficient R hn f c d (hj := hj)) := by
  simp only [postnikovCommonClassStandardGlueLeft, postnikovCommonClassTransitionSource,
    postnikovCommonClassSource, postnikovCommonClassCoefficientMap,
    postnikovCommonClassTransitionMap, postnikovCommonClassCompatibilityToCell,
    postnikovCommonClassCompatibilityCoefficient, Category.assoc, SquareZero.coefficientMap_comp]

lemma postnikovCommonClassStandardGlueRight_eq :
    postnikovCommonClassStandardGlueRight R hn f c d (hj := hj) =
      postnikovCommonClassCompatibilityToCell R hn f c d ≫
        postnikovCellClassOver R (A.obj j).obj (postnikovCommonClassBase R hn f c d) n hn
          (postnikovCommonClassRetractBase R hn f c d (hj := hj)) := by
  simp only [postnikovCommonClassStandardGlueRight, postnikovCommonClassStandardEndpoint,
    postnikovCommonClassStandard, postnikovCommonClassCompatibilityToCell, Category.assoc]

/-- 原仮定から構成した係数逆の class 整合。経路存在は追加入力しない。 -/
def postnikovCommonClassCompatibilityWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R hn f c d (hj := hj)) :=
  postnikovClassBaseZeroWitness R (A.obj j).obj (postnikovCommonClassBase R hn f c d) n hn 1
    (postnikovCommonClassRetractBase R hn f c d (hj := hj))
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R hn f c d (hj := hj))
    (postnikovCommonClassStandardGlueLeft_projection R hn f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight_projection R hn f c d (hj := hj))
    (postnikovCommonClassStandardZeroGlueWitness R hn f c d e)
    (postnikovCommonClassStandardZeroGlueWitness_projection R hn f c d e)

lemma postnikovCommonClassCompatibilityWitness_projection :
    (postnikovCommonClassCompatibilityWitness R hn f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
        postnikovCommonClassStandardGlueProjection R hn f c d ≫
          Path.diagonal R (postnikovCommonClassBase R hn f c d) :=
  postnikovClassBaseZeroWitness_projection _ _ _ _ _ _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
