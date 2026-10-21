module
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEdges
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Core.HomotopyCategoryMap
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C D : Type v) [DGCategory R C] [DGCategory R D]
/-- 元の実 dg nerve 射と同じ閉射の H⁰ 比較。 -/
lemma dgNerveEdgeClosed_map (F : DGFunctor R C D)
    {x y : (dgNerve R C) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve R C)) x y) :
    edgeClosed (e.map ((truncation 2).map (dgNerve.map F))) =
      F.onClosed.map (edgeClosed e) := by
  apply (closedHomEquiv R D _ _).injective
  erw [DGFunctor.closedHomEquiv_map, edgeClosed_cycle, edgeClosed_cycle]
  apply Subtype.ext
  change (edgeCycle (e.map ((truncation 2).map (dgNerve.map F)))).val =
    (F.map (x.obj 0) (y.obj 0)).f 0 (edgeCycle e).val
  have hL := edgeCycle_val_heq (e.map ((truncation 2).map (dgNerve.map F)))
  have hR := dgFunctor_map_component_heq F (edge_source_obj e) (edge_target_obj e) 0
    (edgeCycle_val_heq e).symm
  exact eq_of_heq (hL.trans hR)

/-- 元の実 dg nerve 射と同じ閉射の H⁰ 比較。 -/
lemma dgNerveMap_toH0_naturality (F : DGFunctor R C D) :
    HomotopyCategoryMap.map (dgNerve.map F) ⋙ toH0 R D =
      toH0 R C ⋙ F.onHomotopy := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  rintro _ _ ⟨e⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (toHomotopy R D).map (edgeClosed (e.map ((truncation 2).map (dgNerve.map F)))) =
    F.onHomotopy.map ((toHomotopy R C).map (edgeClosed e))
  rw [dgNerveEdgeClosed_map]
  rfl
end SerrePositivity.InfinityCategories
