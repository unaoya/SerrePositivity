module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerTwoHornDetection
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.InnerTwoHornImageEdges

/-!
概要：同型で表示した内ホーンの像上で辺を保つ元の関手は全ての cocartesian 辺を保つ。
方針：欠ける同じ長辺を元の底の同じ三角形上で二本の辺に分解する。
規約：元の全空間と関手を変更しない。
使われ方：nerve 上の二単体の元の source 制限の自明 Kan 性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同型による内ホーンの同じ像から、元の全 cocartesian 辺の保存を反映する。 -/
lemma preservesCocartesianEdges_of_innerTwoHornImage
    {E F B : SSet.{u}} [Quasicategory B] (s : (Δ[2] : SSet.{u}) ≅ B)
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ B) [InnerFibration q]
    (H : E ⟶ F) (hH : H ≫ q = p)
    (hpres : ∀ e : E _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e →
      p.app (Opposite.op ⦋1⦌) e ∈
        Set.range (((horn 2 1).ι ≫ s.hom).app (Opposite.op ⦋1⦌)) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (H.app (Opposite.op ⦋1⦌) e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q H := by
  intro e he
  by_cases hb : p.app (Opposite.op ⦋1⦌) e ∈
      Set.range (((horn 2 1).ι ≫ s.hom).app (Opposite.op ⦋1⦌))
  · exact hpres e he hb
  have hp : SSet.yonedaEquiv.symm e ≫ p = stdSimplex.δ (1 : Fin 3) ≫ s.hom :=
    (SSet.yonedaEquiv_symm_comp e p).trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.innerTwoHorn_image_missing_edge_eq_long s _ hb)
  obtain ⟨t, htp, hte, hfirst, hsecond⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_cocartesianFactorizationTriangle p e he s.hom hp
  have hmem (j : Fin 3) (hj : j ≠ 1) :
      p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ j ≫ t)) ∈
      Set.range (((horn 2 1).ι ≫ s.hom).app (Opposite.op ⦋1⦌)) := by
    refine ⟨⟨SSet.yonedaEquiv (stdSimplex.δ j),
      (objEquiv_symm_δ_mem_horn_iff j 1).mpr hj⟩, ?_⟩
    change s.hom.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ j)) = _
    rw [← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp, Category.assoc, htp]
  have ha := hpres _ hfirst (hmem 2 (by decide))
  have hc := hpres _ hsecond (hmem 0 (by decide))
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_triangle_longEdge (t ≫ H) q
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using ha)
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using hc)
  have hv : SSet.yonedaEquiv (stdSimplex.δ 1 ≫ (t ≫ H)) =
      H.app (Opposite.op ⦋1⦌) e := by
    rw [← Category.assoc, hte, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rwa [hv] at hl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
