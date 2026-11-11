module
public import SerrePositivity.KST.SConstruction.MultiInnerSCoordinates
public import SerrePositivity.KST.SConstruction.MultiMovingSCore
public import SerrePositivity.KST.SConstruction.InnerDiagonalComponents
public import SerrePositivity.KST.SConstruction.CoordinateZeroPermutation

/-! # 全多次数の座標比較と既存の全対角比較の一致
概要：元の結合子の全多単体的な比較を core へ移し、既存の座標実現同型と照合する。
方針：core 評価と対角を適用し、巡回置換の対角の恒等成分と元の比較成分の等号を使う。
規約：元の座標比較を維持する。使われ方：標準の全零境界商上の巡回自己同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 元の結合子の全多次数の座標比較を core に移した自然同型。 -/
def multiInnerSCoordinateCoreIso (r : ℕ) (X : StableModel.{u}) :
    multiInnerSCoreConstruction r X ≅
      Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) (finRotate (r + 1)) ⋙
        multiCoreSConstruction (r + 1) X :=
  Functor.isoWhiskerRight (multiInnerSCoordinateNatIso r) (stableEndofunctorCoreEvaluation X)

/-- 巡回置換を対角で消した、元の結合子による標準反復への座標同型。 -/
def multiInnerSCoordinateRealizationIso (r : ℕ) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj
        (multiIndexDiagonal (r + 1) ⋙ multiInnerSCoreConstruction r X) ≅
      multiDiagonalCoreSConstruction (r + 1) X :=
  simplicialDiagonalFunctor.mapIso (Functor.isoWhiskerLeft (multiIndexDiagonal (r + 1))
    (multiInnerSCoordinateCoreIso r X)) ≪≫
      coordinatePermutationDiagonalIso (finRotate (r + 1)) (multiCoreSConstruction (r + 1) X)

/-- 全多次数の結合子の座標比較は、既存の元の反復実現の座標比較を厳密に回収する。 -/
lemma multiInnerSCoordinateCoreIso_realization (r : ℕ) (X : StableModel.{u}) :
    (iteratedSMultiInnerRealizationIso r X).hom ≫
      (multiInnerSCoordinateRealizationIso r X).hom =
        (iteratedSRealizationCoordinateIso r X).hom := by
  apply NatTrans.ext
  funext d
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  have h := NatTrans.congr_app
    (diagonalSInnerComparisonNatIso_app_eq_inner r d.unop.len) X
  change (H.map ((multiInnerSCoordinateAt r (fun _ => d)).hom.app X)).app d =
    (H.map (((diagonalSInnerComparisonNatIso r).hom.app d).app X)).app d
  rw [h]
  rfl

end SerrePositivity.KST.SConstruction
