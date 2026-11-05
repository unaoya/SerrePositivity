module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionInputCoordinatesIso
/-! # 正本比較の同一対角と元二入力を同じ座標で保持する

概要：入力付き正本比較を座標同型で移し、元の矢印比較と左右 Hom 鎖射影を厳密に回収する。
方針：外側引き戻しの二射影と、元二入力 lift の射影則を用いる。
規約：矢印座標だけで比較せず、左右 Hom 入力の順序と全時間を保持する。
使われ方：主比較の標的への輸送と、入力付き逆射の接続の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

lemma dgGluingLaxHomInputStrictComparison_raw_pair :
    dgGluingLaxHomInputStrictComparison R C D M X Y ≫
      dgGluingCompositionInputRawPair R C D M X Y =
    lift
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  rw [dgGluingCompositionInputRawPair, dgGluingRestrictedDiagonalInputPair]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
    rw [← Category.assoc]
    erw [dgGluingLaxHomInputStrictComparison_last R C D M X Y]
    exact dgGluingLaxHomLastCompositionInputLift_input R C D M X Y
  · simp only [Category.assoc, lift_snd]
    rw [← Category.assoc]
    erw [dgGluingLaxHomInputStrictComparison_first R C D M X Y]
    exact dgGluingLaxHomFirstCompositionInputLift_input R C D M X Y

def dgGluingLaxHomInputCoordinateComparison :=
  dgGluingLaxHomInputStrictComparison R C D M X Y ≫
    (dgGluingCompositionInputStrictCoordinatesIso R C D M X Y).hom

lemma dgGluingLaxHomInputCoordinateComparison_arrow :
    dgGluingLaxHomInputCoordinateComparison R C D M X Y ≫ pullback.fst _ _ =
      dgGluingLaxHomArrowCompositionComparison R C D M X Y := by
  rw [dgGluingLaxHomInputCoordinateComparison, Category.assoc,
    dgGluingCompositionInputStrictCoordinatesIso_forget R C D M X Y,
    dgGluingLaxHomInputStrictComparison_forget R C D M X Y]

lemma dgGluingLaxHomInputCoordinateComparison_inputs :
    dgGluingLaxHomInputCoordinateComparison R C D M X Y ≫ pullback.snd _ _ =
    lift
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)))
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) := by
  rw [dgGluingLaxHomInputCoordinateComparison, Category.assoc,
    dgGluingCompositionInputStrictCoordinatesIso_inputs R C D M X Y,
    dgGluingLaxHomInputStrictComparison_raw_pair R C D M X Y]
end SerrePositivity.InfinityCategories
