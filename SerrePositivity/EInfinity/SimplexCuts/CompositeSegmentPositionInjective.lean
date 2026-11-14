module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSegmentInnerVertices

/-!
# 同じ合成位置の元の部分語と相対位置

Berger–Fresse §2.2.6、M14 L12a のC451の指定位置の法則。
異なる部分語の位置は交わらず、同じ部分語では元の接頭長を消去する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の部分語と相対位置は、同じ合成位置から一意に決まる（BF §2.2.6）。 -/
lemma positiveCompositeSegmentPosition_sigma_injective {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e)) :
    Function.Injective (fun s : Σ i, Fin (r.val i).val =>
      positiveCompositeSegmentPosition u v k r s.1 s.2) := by
  rintro ⟨i, z⟩ ⟨j, w⟩ h
  change positiveCompositeSegmentPosition u v k r i z =
    positiveCompositeSegmentPosition u v k r j w at h
  have hij : i = j := by
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have ho : (positiveCompositeSegmentPosition u v k r i z).val <
          (positiveCompositeSegmentPosition u v k r j w).val :=
        IntervalCuts.compositeSegmentPosition_lt u v k r i j hlt z w
      have he := congrArg Fin.val h
      omega
    · exact heq
    · have ho : (positiveCompositeSegmentPosition u v k r j w).val <
          (positiveCompositeSegmentPosition u v k r i z).val :=
        IntervalCuts.compositeSegmentPosition_lt u v k r j i hgt w z
      have he := congrArg Fin.val h
      omega
  subst j
  have hzw : z = w := by
    apply Fin.ext
    have he := congrArg Fin.val h
    simp only [positiveCompositeSegmentPosition_val] at he
    omega
  exact congrArg (fun t => Sigma.mk i t) hzw

/-- 同じ元の挿入位置の分解は、同じ内側頂点を与える（BF §2.2.6）。 -/
lemma positiveCompositeSegmentInnerVertex_eq_of_same_source {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) (z : Fin (c.1.val i).val)
    (x : Fin (m + n + (d + e) + q + 1))
    (hx : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 i z)
    (j : Fin (Surjection.occurrenceCount u.val k)) (w : Fin (c.1.val j).val)
    (hy : c.2.horizontal x = positiveCompositeSegmentPosition u v k c.1 j w) :
    positiveCompositeSegmentInnerVertex u v k c i z x hx =
      positiveCompositeSegmentInnerVertex u v k c j w x hy := by
  have hs : (⟨i, z⟩ : Σ i, Fin (c.1.val i).val) = ⟨j, w⟩ :=
    positiveCompositeSegmentPosition_sigma_injective u v k c.1 (hx.symm.trans hy)
  cases hs
  rfl

end SerrePositivity.EInfinity.SimplexCuts
