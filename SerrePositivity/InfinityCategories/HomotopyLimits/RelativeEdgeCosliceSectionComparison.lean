module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeEdgeCosliceSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeCosliceFamilyHomotopy

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 同じ終点と指定した底を持つ族は、普遍切断の像と両者を全時刻固定して比較できる。 -/
lemma exists_relativeEdgeCosliceSection_comparison {E B T : SSet.{u}} [Quasicategory B]
    (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B) [InnerFibration q]
    (a : T ⟶ sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e)) (b : T ⟶ sliceUnder e)
    (hterminal : b ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = a)
    (hbase : b ≫ sliceUnderPostcomp e q =
      a ≫ sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q)) :
    ∃ H : SSet.Homotopy (a ≫ relativeEdgeCosliceSection e q) b,
      H.h ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = fst T Δ[1] ≫ a ∧
      H.h ≫ sliceUnderPostcomp e q = fst T Δ[1] ≫ a ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q) := by
  have ht : (a ≫ relativeEdgeCosliceSection e q) ≫
      sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) =
      b ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) := by
    rw [Category.assoc, relativeEdgeCosliceSection_target, Category.comp_id, hterminal]
  have hb : (a ≫ relativeEdgeCosliceSection e q) ≫ sliceUnderPostcomp e q =
      b ≫ sliceUnderPostcomp e q := by
    rw [Category.assoc, relativeEdgeCosliceSection_base, hbase]
  obtain ⟨H, hHt, hHb⟩ := exists_relativeCosliceFamilyHomotopy e q
    (stdSimplex.δ (0 : Fin 2)) endpointInclusion_rightAnodyne
    (a ≫ relativeEdgeCosliceSection e q) b ht hb
  refine ⟨H, ?_, ?_⟩
  · simpa only [hterminal] using hHt
  · simpa only [hbase, Category.assoc] using hHb

end SerrePositivity.InfinityCategories.HomotopyLimits
