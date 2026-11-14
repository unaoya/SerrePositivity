module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointInverse
public import SerrePositivity.EInfinity.SimplexCuts.DegenerateHorizontalTerms

/-!
# nullaryの一頂点削除の非退化性と元の残り色の面

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §324。
元の全頂点列・同じ水平境界の削除座標・退化零項を保って比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の切断が非退化なら、一頂点を削除したraw語も非退化（BF §2.2.6）。 -/
lemma erased_word_nondegenerate_of_point_cut_nondegenerate {m q r : ℕ}
    (s : Cut (m + 1) q) (v : Surjection.Word r (m + 2)) (p : Fin (m + 2))
    (hpoint : hi s p = lo s p) (hcut : Nondegenerate s v.val) :
    Surjection.Nondegenerate (Surjection.erase v.val p) := by
  obtain ⟨j, hj⟩ := s.horizontal_surjective p
  have hk : boundaryVertexKind s j = .horizontal := by
    apply (boundaryVertexKind_eq_horizontal_gap s j).mpr
    refine ⟨by omega, ?_⟩
    rw [hj, hpoint, Nat.sub_self]
  have hhor := ((boundaryVertexKind_eq_horizontal_iff s j).mp hk).2
  by_contra hdeg
  have hd : ¬Surjection.Nondegenerate (Surjection.erase v.val (s.horizontal j)) := by
    simpa only [hj] using hdeg
  obtain ⟨c, _, hc⟩ := other_face_not_mono_horizontal_degenerate s v j hhor hd
  exact hc ((faces_mono_iff s v).mpr hcut c)

end SerrePositivity.EInfinity.SimplexCuts
