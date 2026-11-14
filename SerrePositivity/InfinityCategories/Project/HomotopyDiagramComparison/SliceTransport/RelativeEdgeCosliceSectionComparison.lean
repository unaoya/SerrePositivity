module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.RelativeEdgeCosliceSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.RelativeCosliceFamilyHomotopy

/-!
概要：普遍的な相対辺切断の像を、同じ終点と底を持つ元の全辺族へ比較する。
方針：相対 coslice の終点制限の fiber で比較し、境界と底を全時刻で固定する。
規約：切断の前合成自然性は仮定しない。使われ方：前置後の族と元の根辺三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 同じ終点と指定した底を持つ族は、普遍切断の像と両者を全時刻固定して比較できる。 -/
lemma exists_relativeEdgeCosliceSection_comparison {E B T : SSet.{u}} [Quasicategory B]
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e)) (b : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder e)
    (hterminal : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = a)
    (hbase : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q =
      a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (e ≫ q)) :
    ∃ H : SSet.Homotopy (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) b,
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = fst T Δ[1] ≫ a ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q = fst T Δ[1] ≫ a ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSection (e ≫ q) := by
  have ht : (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_target, Category.comp_id, hterminal]
  have hb : (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp e q := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection_base, hbase]
  obtain ⟨H, hHt, hHb⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_relativeCosliceFamilyHomotopy e q
    (stdSimplex.δ (0 : Fin 2)) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.endpointInclusion_rightAnodyne
    (a ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeCosliceSection e q) b ht hb
  refine ⟨H, ?_, ?_⟩
  · simpa only [hterminal] using hHt
  · simpa only [hbase, Category.assoc] using hHb

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
