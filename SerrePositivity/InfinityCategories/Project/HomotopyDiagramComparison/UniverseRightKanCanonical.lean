module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseRightKanShape
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniversePointCosliceUncurry
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ReindexSliceOver
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightCanonicalMapping

/-!
概要：右 Kan 標準全錐の宇宙変更は、元の局所添字の同型を介して厳密に一致する。
方針：元の coslice 射影の一致と、同じ全普遍錐族の展開の宇宙比較を使う。
規約：元の関手と指定点と全錐写像を保持する。
使われ方：元の Hom 全族の局所極限を、持ち上げた元の右 Kan 条件へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の右 Kan 添字の宇宙同型は、同じ標準全錐の写像そのものを保つ。 -/
lemma rightKanCanonicalCone_universe_val {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{max u v})) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanShapeUniverseIso.{u, v} δ c).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
          ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)).val := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry _ ≫ _) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanShapeUniverseIso_slice, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointCosliceUniverseIso_uncurry]
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _ 0).inv ≫ (SSet.uliftFunctor.{v, u}).map _) ≫
      (SSet.uliftFunctor.{v, u}).map F =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso _ 0).inv ≫ (SSet.uliftFunctor.{v, u}).map (_ ≫ F)
  rw [Functor.map_comp, Category.assoc]

/-- 元の右 Kan 標準全錐の極限性は、同じ元の宇宙持ち上げの標準全錐と同値。 -/
lemma rightKanCanonicalCone_isLimit_iff_ulift {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
        ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)) := by
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
    ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanShapeUniverseIso.{u, v} δ c
  apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_ulift (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)).trans
  apply Iff.trans ?_ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso d e).symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq
  · dsimp only [d, e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanShapeUniverseIso_projection]
  · exact (rightKanCanonicalCone_universe_val δ F c).symm

/-- 元の標準錐の持ち上げの指定像が極限なら、同じ後合成の標準右 Kan 錐も極限。 -/
lemma rightKanCanonicalCone_post_ulift_isLimit {K C D : SSet.{u}} {E : SSet.{max u v}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌)
    (q : (SSet.uliftFunctor.{v, u}).obj D ⟶ E)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map F ≫ q) (ULift.up c)) := by
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
    ((SSet.uliftFunctor.{v, u}).map F ≫ q) (ULift.up c)
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanShapeUniverseIso.{u, v} δ c
  apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isLimitCone_iff_reindexIso d e).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_of_diagram_eq (c := d.reindexIso e)
    (d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c))) ?_ ?_).mpr hc
  · dsimp only [d, e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanShapeUniverseIso_projection]
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) e.hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone ((SSet.uliftFunctor.{v, u}).map δ)
        ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val ≫ q) = _
    rw [← Category.assoc, rightKanCanonicalCone_universe_val]
    rfl

/-- 元の全標準錐像の極限性は、持ち上げた元の射への実際の右 Kan 条件を与える。 -/
lemma rightKanExtension_refl_post_ulift_of_canonicalLimits
    {K C D : SSet.{u}} {E : SSet.{max u v}}
    (δ : K ⟶ C) (F : C ⟶ D) (q : (SSet.uliftFunctor.{v, u}).obj D ⟶ E)
    (h : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map δ ≫ ((SSet.uliftFunctor.{v, u}).map F ≫ q))
      ((SSet.uliftFunctor.{v, u}).map F ≫ q)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl
        ((SSet.uliftFunctor.{v, u}).map δ ≫ ((SSet.uliftFunctor.{v, u}).map F ≫ q))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanExtension_refl_of_canonicalLimits
  rintro ⟨c⟩
  exact rightKanCanonicalCone_post_ulift_isLimit δ F c q (h c)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
