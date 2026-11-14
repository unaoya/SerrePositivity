module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：元の dg nerve 射の実辺と二切断の H⁰ 比較を、同じ dg 関手の作用へ照合する。
方針：実閉 cycle の異種等号を端点の移送ごと保持し、辺の商の代表上で比較する。
規約：大きい dg 圏の Small 性を仮定しない。使われ方：一般 RHom の ∞ 随伴の H⁰ 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 元の実 dg nerve 射と同じ閉射の H⁰ 比較。 -/
lemma dgNerveEdgeClosed_map (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D)
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) x y) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))) =
      F.onClosed.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e) := by
  apply (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D _ _).injective
  erw [DGFunctor.closedHomEquiv_map, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle]
  apply Subtype.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)))).val =
    (F.map (x.obj 0) (y.obj 0)).f 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle e).val
  have hL := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)))
  have hR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_map_component_heq F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_source_obj e) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edge_target_obj e) 0
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq e).symm
  exact eq_of_heq (hL.trans hR)

/-- 元の実 dg nerve 射と同じ閉射の H⁰ 比較。 -/
lemma dgNerveMap_toH0_naturality (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 R C ⋙ F.onHomotopy := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  rintro _ _ ⟨e⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (toHomotopy R D).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)))) =
    F.onHomotopy.map ((toHomotopy R C).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e))
  rw [dgNerveEdgeClosed_map]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
