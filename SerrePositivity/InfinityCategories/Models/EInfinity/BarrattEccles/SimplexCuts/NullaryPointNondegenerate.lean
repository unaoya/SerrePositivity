module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPointInverse
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.DegenerateHorizontalTerms

/-!
模型。文献の定義との比較は後で
# nullaryの一頂点削除の非退化性と元の残り色の面

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §324。
元の全頂点列・同じ水平境界の削除座標・退化零項を保って比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の切断が非退化なら、一頂点を削除したraw語も非退化（BF §2.2.6）。 -/
lemma erased_word_nondegenerate_of_point_cut_nondegenerate {m q r : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (m + 1) q) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 2)) (p : Fin (m + 2))
    (hpoint : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p) (hcut : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Nondegenerate s v.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val p) := by
  obtain ⟨j, hj⟩ := s.horizontal_surjective p
  have hk : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind s j = .horizontal := by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_horizontal_gap s j).mpr
    refine ⟨by omega, ?_⟩
    rw [hj, hpoint, Nat.sub_self]
  have hhor := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryVertexKind_eq_horizontal_iff s j).mp hk).2
  by_contra hdeg
  have hd : ¬_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v.val (s.horizontal j)) := by
    simpa only [hj] using hdeg
  obtain ⟨c, _, hc⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.other_face_not_mono_horizontal_degenerate s v j hhor hd
  exact hc ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.faces_mono_iff s v).mpr hcut c)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
