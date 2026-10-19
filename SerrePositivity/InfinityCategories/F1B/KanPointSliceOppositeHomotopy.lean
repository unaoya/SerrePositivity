module

public import SerrePositivity.InfinityCategories.F1B.KanPointSliceOppositeUncurry
public import SerrePositivity.InfinityCategories.F1B.KanMappingPrismOpposite
public import SerrePositivity.InfinityCategories.F1B.KanPointSliceHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanRightKanShapeCommaComparison
public import SerrePositivity.InfinityCategories.F1B.KanFunctorOpposite

/-!
概要：点の slice の標準指定変換の反転は coslice の標準指定変換と一致する。
方針：普遍余錐の反転と、左右の円柱比較の反転を合成する。
規約：両変換は実際の円柱の射として比較する。
使われ方：左 Kan の局所添字の反転比較が標準の矢印を表すことの証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：slice の標準変換の時間を第一因子へ直すと右の点付き円柱による展開となる。
方針：点を補う射と二因子を交換する射の成分を計算する。
規約：パラメータ A は任意。
使われ方：標準変換の反転を左右円柱の比較に帰着する。 -/
lemma kanPointSliceHomotopy_prism {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ sliceOver (SSet.yonedaEquiv.symm x)) :
    (β_ (Δ[1] : SSet.{u}) A).hom ≫ (kanPointSliceHomotopy x f).h =
      rightMappingSpacePrism A ≫ sliceOverUncurry f := rfl

/-- 概要：正規化した反転の coslice の指定変換は元の slice の指定変換の反転。
方針：普遍錐の反転公式と、右の円柱の反転の公式を後合成する。
規約：quasicategory 性を使わない。
使われ方：局所添字の比較が標準の指定変換を保つことの入力。 -/
lemma kanPointSliceOverOpIso_homotopy {A X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ sliceOver (SSet.yonedaEquiv.symm x)) :
    (kanPointCosliceHomotopy (SSet.opObjEquiv.symm x)
      (SSet.opFunctor.map f ≫ (cofinalPointSliceOverOpIso x).hom.left)).h =
        (kanHomotopyOpposite (kanPointSliceHomotopy x f)).h := by
  have hp : reversePrism (rightMappingSpacePrism A) =
      leftMappingSpacePrism A.op ≫ joinMap (stdSimplex.opIso ⦋0⦌).inv (𝟙 A.op) ≫
        (stableJoinReverseIso A Δ[0]).inv := by
    have h := congrArg (fun z ↦ z ≫ (stableJoinReverseIso A Δ[0]).inv)
      (kanRightMappingSpacePrism_reverse A)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  dsimp only [kanPointCosliceHomotopy, kanHomotopyOpposite]
  rw [kanPointSliceOverOpIso_uncurry, kanPointSliceHomotopy_prism,
    reversePrism_postcomp, hp]
  simp only [Category.assoc]

end SerrePositivity.InfinityCategories.F1B
