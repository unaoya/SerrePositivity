module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerVertices

/-!
# 元の内側頂点から合成切断の同じ頂点を特定する

Berger–Fresse §2.2.6、M14 L12a のC451の全頂点の比較。
同じ色別順位は同じ外側区間を特定し、同じ内側位置は同じ相対位置を特定する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ内側頂点を与える元の挿入頂点は等しい（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_source_injective {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (y : Fin (m + n + (d + e) + q + 1))
    (hy : c.2.horizontal y = positiveCompositeSegmentPosition u v k c.1 j w)
    (h : positiveCompositeSegmentInnerVertex u v k c i z x hx =
      positiveCompositeSegmentInnerVertex u v k c j w y hy) : x = y := by
  have hcx := positiveCompositeSegmentInnerVertex_coordinates u v k c i z x hx
  have hcy := positiveCompositeSegmentInnerVertex_coordinates u v k c j w y hy
  have hr := congrArg (positiveCompositeInnerCut u v k c).vertical h
  rw [hcx.2, hcy.2] at hr
  have hmi := positiveCompositeSegmentVertexRank_mem u v k c i z x hx
  have hmj := positiveCompositeSegmentVertexRank_mem u v k c j w y hy
  have hpi := (Finset.mem_filter.mp hmi).2
  have hpj := (Finset.mem_filter.mp hmj).2
  rw [hr] at hpi
  have hij : i = j := (positiveOccurrencePosition_strictMono u k).injective (hpi.symm.trans hpj)
  subst j
  have hj := congrArg (positiveCompositeInnerCut u v k c).horizontal h
  rw [hcx.1, hcy.1] at hj
  have hzw : z = w := by
    apply Fin.ext
    have hval := congrArg Fin.val hj
    change c.1.start i + z.val = c.1.start i + w.val at hval
    omega
  subst w
  apply c.2.vertex_injective
  apply Prod.ext
  · exact hx.trans hy.symm
  · have hv := congrArg (fun t => vertices (positiveCompositeOuterCut u v k c)
      (positiveWord u) k ((positiveCompositeInnerCut u v k c).vertical t)) h
    rw [positiveCompositeSegmentInnerVertex_vertices,
      positiveCompositeSegmentInnerVertex_vertices] at hv
    exact hv

end SerrePositivity.EInfinity.SimplexCuts
