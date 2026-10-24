module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroWitness

/-!
概要：細分後の係数逆で移した源 class と、元の低い段の標準 class の実相対経路。
方針：零標的で貼り合わせた経路を、元の class 標的へ実底変更で戻す。
規約：元の係数逆・遷移・両 class と次数全射準同型の源射影を保持。使われ方：二切断逆。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassCompatibilityCoefficient :
    postnikovOneRoofShiftedDenominatorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1 ⟶
        postnikovCommonClassTransitionLayer R f c d hj :=
  postnikovCommonShiftedCoefficientMap R f c d 1 ≫
    postnikovCommonClassTransitionCoefficient R f c d hj

def postnikovCommonClassCompatibilityToCell : postnikovCommonClassStandardGlueSource R f c d ⟶
    cellResolution R (postnikovCommonClassBase R f c d) :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    postnikovCommonRightGlueToCell R f c d

lemma postnikovCommonClassCompatibilityToCell_projection :
    postnikovCommonClassCompatibilityToCell R f c d ≫
      cellAugmentation R (postnikovCommonClassBase R f c d) =
        postnikovCommonClassStandardGlueProjection R f c d := by
  rw [postnikovCommonClassCompatibilityToCell, Category.assoc,
    postnikovCommonRightGlueToCell_projection]
  rfl

lemma postnikovCommonClassStandardGlueLeft_eq :
    postnikovCommonClassStandardGlueLeft R f c d (hj := hj) =
      postnikovCommonClassCompatibilityToCell R f c d ≫
        postnikovCellClassOver R (B.obj d.zero.stage).obj (postnikovCommonClassBase R f c d)
          1 (by omega) (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
            SquareZero.coefficientMap (postnikovCommonClassBase R f c d)
              (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)) := by
  simp only [postnikovCommonClassStandardGlueLeft, postnikovCommonClassTransitionSource,
    postnikovCommonClassSource, postnikovCommonClassCoefficientMap,
    postnikovCommonClassTransitionMap, postnikovCommonClassCompatibilityToCell,
    postnikovCommonClassCompatibilityCoefficient, Category.assoc, SquareZero.coefficientMap_comp]
  rfl

lemma postnikovCommonClassStandardGlueRight_eq :
    postnikovCommonClassStandardGlueRight R f c d (hj := hj) =
      postnikovCommonClassCompatibilityToCell R f c d ≫
        postnikovCellClassOver R (A.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
          (postnikovCommonClassRetractBase R f c d (hj := hj)) := by
  simp only [postnikovCommonClassStandardGlueRight, postnikovCommonClassStandardEndpoint,
    postnikovCommonClassStandard, postnikovCommonClassCompatibilityToCell, Category.assoc]

/-- 原仮定から構成した係数逆の class 整合。経路存在は追加入力しない。 -/
def postnikovCommonClassCompatibilityWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj)) :=
  postnikovClassBaseZeroWitness R (A.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega) 1
    (postnikovCommonClassRetractBase R f c d (hj := hj))
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj))
    (postnikovCommonClassStandardGlueLeft_projection R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight_projection R f c d (hj := hj))
    (postnikovCommonClassStandardZeroGlueWitness R f c d e)
    (postnikovCommonClassStandardZeroGlueWitness_projection R f c d e)

lemma postnikovCommonClassCompatibilityWitness_projection :
    (postnikovCommonClassCompatibilityWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
        postnikovCommonClassStandardGlueProjection R f c d ≫
          Path.diagonal R (postnikovCommonClassBase R f c d) :=
  postnikovClassBaseZeroWitness_projection _ _ _ _ _ _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
