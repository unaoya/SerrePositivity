module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoin
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ReindexSliceOver
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseHorns
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseOuterHornJoins
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareCompatibility
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareShape

/-! # 普遍四角形の宇宙降下

概要：実四角形の引き戻し性・押し出し性は ULift で保ち反映される。
方針：持ち上げた錐をホーン同型で再添字付けし、同じ実錐写像へ戻す。
規約：標的の quasicategory 性は不要。使われ方：安定性と dg nerve の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet MonoidalCategory
open scoped _root_.Simplicial

/-- 同じ実錐写像は固定図式の証明によらず同じ普遍性を持つ。 -/
lemma isLimitCone_iff_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d := by
  have hp : p = q := by rw [← c.property, ← d.property, h]
  subst q
  have hc : c = d := Subtype.ext h
  subst d
  rfl

/-- 同じ実錐写像は固定図式の証明によらず同じ普遍性を持つ。 -/
lemma isColimitCone_iff_of_val_eq {K X : SSet.{u}} {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  have hp : p = q := by rw [← c.property, ← d.property, h]
  subst q
  have hc : c = d := Subtype.ext h
  subst d
  rfl

/-- 持ち上げた標準錐を再添字付けすると持ち上げた四角形の実錐となる。 -/
lemma pullbackCone_ulift_reindex_val {X : SSet.{u}}
    (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).ulift).reindexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 2).symm).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare F)).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 2).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ F)) = _
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 2).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _ 0).inv =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso.{u, v}.inv := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso
    simp only [Iso.trans_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.refl_inv, ← Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, hs]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso_square.{u, v}
  have hi : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso.{u, v}.inv ≫
      (SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.inv := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Functor.map_comp, ← Category.assoc, hi]
  rfl

/-- 実Pullback四角形の普遍性は宇宙比較で保ち反映される。 -/
lemma isPullbackSquare_iff_ulift {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} F) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_ulift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso _ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 2).symm).trans
      (isLimitCone_iff_of_val_eq _ _ (pullbackCone_ulift_reindex_val F)))

/-- 持ち上げた標準錐を再添字付けすると持ち上げた四角形の実錐となる。 -/
lemma pushoutCocone_ulift_reindex_val {X : SSet.{u}}
    (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F).ulift).reindexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 0).symm).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare F)).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 0).inv (𝟙 _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ F)) = _
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso 2 0).inv (𝟙 _) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso _ 0).inv =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso.{u, v}.inv := by
    unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso
    simp only [Iso.trans_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.refl_inv, ← Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, hs]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso_square.{u, v}
  have hi : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso.{u, v}.inv ≫
      (SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.inv := by
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ht, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Functor.map_comp, ← Category.assoc, hi]
  rfl

/-- 実Pushout四角形の普遍性は宇宙比較で保ち反映される。 -/
lemma isPushoutSquare_iff_ulift {X : SSet.{u}} (F : Δ[1] ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquare.{u, v} F) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_ulift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone F)).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isColimitCone_iff_reindexIso _ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, v} 2 0).symm).trans
      (isColimitCone_iff_of_val_eq _ _ (pushoutCocone_ulift_reindex_val F)))

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
