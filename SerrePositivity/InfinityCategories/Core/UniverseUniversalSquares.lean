module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.Core.UniverseJoin
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.ReindexSliceOver
public import SerrePositivity.InfinityCategories.Core.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.Core.UniverseHorns
public import SerrePositivity.InfinityCategories.Core.UniverseOuterHornJoins
public import SerrePositivity.InfinityCategories.Core.UniverseSquareCompatibility
public import SerrePositivity.InfinityCategories.Core.UniverseSquareShape

/-! # 普遍四角形の宇宙降下

概要：実四角形の引き戻し性・押し出し性は ULift で保ち反映される。
方針：持ち上げた錐をホーン同型で再添字付けし、同じ実錐写像へ戻す。
規約：標的の quasicategory 性は不要。使われ方：安定性と dg nerve の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits MonoidalCategory
open scoped Simplicial

/-- 同じ実錐写像は固定図式の証明によらず同じ普遍性を持つ。 -/
lemma isLimitCone_iff_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCone p) (d : JoinCone q) (h : c.val = d.val) :
    IsLimitCone c ↔ IsLimitCone d := by
  have hp : p = q := by rw [← c.property, ← d.property, h]
  subst q
  have hc : c = d := Subtype.ext h
  subst d
  rfl

/-- 同じ実錐写像は固定図式の証明によらず同じ普遍性を持つ。 -/
lemma isColimitCone_iff_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (h : c.val = d.val) :
    IsColimitCone c ↔ IsColimitCone d := by
  have hp : p = q := by rw [← c.property, ← d.property, h]
  subst q
  have hc : c = d := Subtype.ext h
  subst d
  rfl

/-- 持ち上げた標準錐を再添字付けすると持ち上げた四角形の実錐となる。 -/
lemma pullbackCone_ulift_reindex_val {X : SSet.{u}}
    (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (((pullbackCone F).ulift).reindexIso (uliftHornIso.{u, v} 2 2).symm).val =
      (pullbackCone (uliftSquare F)).val := by
  change joinMap (𝟙 _) (uliftHornIso 2 2).inv ≫
    ((uliftConeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (cospanConeSquareIso.hom ≫ F)) = _
  have hs : joinMap (𝟙 _) (uliftHornIso 2 2).inv ≫ (uliftConeShapeIso _ 0).inv =
      uliftCospanConeIso.{u, v}.inv := by
    unfold uliftConeShapeIso uliftCospanConeIso
    simp only [Iso.trans_inv, joinIso, Iso.refl_inv, ← Category.assoc,
      ← joinMap_comp, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, hs]
  have ht := uliftCospanConeIso_square.{u, v}
  have hi : uliftCospanConeIso.{u, v}.inv ≫
      (SSet.uliftFunctor.{v, u}).map cospanConeSquareIso.hom =
        cospanConeSquareIso.hom ≫ uliftSquareIso.inv := by
    apply (cancel_mono uliftSquareIso.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Functor.map_comp, ← Category.assoc, hi]
  rfl

/-- 実Pullback四角形の普遍性は宇宙比較で保ち反映される。 -/
lemma isPullbackSquare_iff_ulift {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPullbackSquare F ↔ IsPullbackSquare (uliftSquare.{u, v} F) :=
  (isLimitCone_iff_ulift (pullbackCone F)).trans
    ((isLimitCone_iff_reindexIso _ (uliftHornIso.{u, v} 2 2).symm).trans
      (isLimitCone_iff_of_val_eq _ _ (pullbackCone_ulift_reindex_val F)))

/-- 持ち上げた標準錐を再添字付けすると持ち上げた四角形の実錐となる。 -/
lemma pushoutCocone_ulift_reindex_val {X : SSet.{u}}
    (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (((pushoutCocone F).ulift).reindexIso (uliftHornIso.{u, v} 2 0).symm).val =
      (pushoutCocone (uliftSquare F)).val := by
  change joinMap (uliftHornIso 2 0).inv (𝟙 _) ≫
    ((uliftCoconeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (spanCoconeSquareIso.hom ≫ F)) = _
  have hs : joinMap (uliftHornIso 2 0).inv (𝟙 _) ≫ (uliftCoconeShapeIso _ 0).inv =
      uliftSpanCoconeIso.{u, v}.inv := by
    unfold uliftCoconeShapeIso uliftSpanCoconeIso
    simp only [Iso.trans_inv, joinIso, Iso.refl_inv, ← Category.assoc,
      ← joinMap_comp, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, hs]
  have ht := uliftSpanCoconeIso_square.{u, v}
  have hi : uliftSpanCoconeIso.{u, v}.inv ≫
      (SSet.uliftFunctor.{v, u}).map spanCoconeSquareIso.hom =
        spanCoconeSquareIso.hom ≫ uliftSquareIso.inv := by
    apply (cancel_mono uliftSquareIso.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Functor.map_comp, ← Category.assoc, hi]
  rfl

/-- 実Pushout四角形の普遍性は宇宙比較で保ち反映される。 -/
lemma isPushoutSquare_iff_ulift {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    IsPushoutSquare F ↔ IsPushoutSquare (uliftSquare.{u, v} F) :=
  (isColimitCone_iff_ulift (pushoutCocone F)).trans
    ((isColimitCone_iff_reindexIso _ (uliftHornIso.{u, v} 2 0).symm).trans
      (isColimitCone_iff_of_val_eq _ _ (pushoutCocone_ulift_reindex_val F)))

end SerrePositivity.InfinityCategories
