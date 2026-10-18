module
public import SerrePositivity.InfinityCategories.Stable.SquareOppositeShapes
public import SerrePositivity.InfinityCategories.Stable.ColimitReindex
public import SerrePositivity.InfinityCategories.Stable.PastingRightCocone

/-! # 引き戻し四角形と反転した押し出し四角形

概要：引き戻し性は両座標と値域を反転した四角形の押し出し性と同値。
方針：極限錐の反転、ホーンの同型、四角形の形状の厳密な比較を合成する。
規約：値域の quasicategory 性は不要。
使われ方：S4 の引き戻しの貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転した錐の射は join の反転と標準零単体の表示で得られる。
方針：slice の反転の各次数の式を零次数に適用する。
規約：元の錐の基底は任意。使われ方：普遍四角形の比較。 -/
lemma JoinCone.reverseCocone_val {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    c.reverseCocone.val =
      joinMap (𝟙 K.op) (stdSimplex.opIso ⦋0⦌).inv ≫
        (stableJoinReverseIso Δ[0] K).inv ≫ SSet.opFunctor.map c.val := by
  have h := sliceOverOpObjEquiv_val p ⦋0⦌
    (SSet.opObjEquiv.symm (show (sliceOver p) _⦋0⦌ from c))
  unfold JoinCone.reverseCocone
  change (sliceOverOpObjEquiv p ⦋0⦌
    (SSet.opObjEquiv.symm (show (sliceOver p) _⦋0⦌ from c))).val = _
  simpa only [Equiv.apply_symm_apply] using h

/-- 概要：引き戻し四角形は反転すると押し出し四角形となり、その逆も成り立つ。
方針：反転した極限錐を標準 span に制限し、余錐の射の等式で比較する。
規約：値域への追加の仮定なし。使われ方：引き戻しの貼り合わせの双対化。 -/
lemma isPullbackSquare_iff_reverseGrid {X : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare F ↔ IsPushoutSquare (reverseGrid F) := by
  refine (isLimitCone_iff_reverseCocone_restrict (pullbackCone F)
    (hornReverseIso 2 2).hom).trans ?_
  apply isColimitCone_iff_of_val_eq
  change joinMap (hornReverseIso 2 2).hom (𝟙 Δ[0]) ≫
    (pullbackCone F).reverseCocone.val = spanCoconeSquareIso.hom ≫ reverseGrid F
  rw [JoinCone.reverseCocone_val]
  change joinMap (hornReverseIso 2 2).hom (𝟙 Δ[0]) ≫
    joinMap (𝟙 _) (stdSimplex.opIso ⦋0⦌).inv ≫
    (stableJoinReverseIso Δ[0] (horn 2 2 : SSet.{u})).inv ≫
    SSet.opFunctor.map (cospanConeSquareIso.hom ≫ F) = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.comp_id, Category.id_comp, CategoryTheory.Functor.map_comp]
  change squareConeReverseShape ≫ SSet.opFunctor.map cospanConeSquareIso.hom ≫
    SSet.opFunctor.map F = _
  rw [← Category.assoc, squareConeReverseShape_square, Category.assoc]
  rw [← reverseGrid_postcomp, Category.id_comp]

end SerrePositivity.InfinityCategories
