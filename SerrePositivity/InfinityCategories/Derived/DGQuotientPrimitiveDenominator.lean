module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFiniteBoundaryCancellation
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition

/-! # 商で指定された原始元に対する元の実分母と原始元

概要：商で原始元を持つ閉元に、元の閉実分母と元の Hom の原始元を回収する。
方針：有限族の同時零化を一点族に適用し、実辺の閉射を厳密に戻す。
規約：指定された商の原始元は残差の入力として保持する。使われ方：相対持ち上げの第一段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商に原始元を持つ元の閉元に、閉実分母と同じ次数の元の原始元が存在する。 -/
theorem dgQuotientBoundary_exists_closedPrimitive (P : Set D) (hP : localKFlat A D P)
    (x y : D) (k : ℤ) (a : GradedHom A x y (k + 1)) (ha : differential A a = 0)
    (c : GradedHom A ((inclusion A D P).obj x) ((inclusion A D P).obj y) k)
    (hc : differential A c = ((inclusion A D P).map x y).f (k + 1) a) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
      ∃ h : GradedHom A q y k,
        differential A h = dgGradedPrecompose A D (k + 1) a s := by
  have hk : k + 1 - 1 = k := by omega
  have hb (i : Fin 1) : ∃ b : GradedHom A ((inclusion A D P).obj x)
      ((inclusion A D P).obj y) (k + 1 - 1),
      (homObject A (QuotientObject D P) ((inclusion A D P).obj x)
        ((inclusion A D P).obj y)).d (k + 1 - 1) (k + 1) b =
          ((inclusion A D P).map x y).f (k + 1) a := by
    rw [hk]
    exact ⟨c, hc⟩
  obtain ⟨q, t, ht, hp⟩ := dgQuotientFiniteBoundary_exists_primitives A D P hP
    x (fun _ : Fin 1 => y) (fun _ => k + 1) (fun _ => a) (fun _ => ha) hb
  have h0 := hp 0
  change (∃ h : GradedHom A q y (k + 1 - 1),
    (homObject A D q y).d (k + 1 - 1) (k + 1) h =
      compose A (D := D) (x := q) (y := x) (z := y) a
        (closedHomEquiv A D _ _ (edgeClosed t)).val (zero_add (k + 1))) at h0
  rw [hk] at h0
  obtain ⟨h, hh⟩ := h0
  let s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x := edgeClosed t
  have hs : dgClosedEdge A D s = t := dgClosedEdge_edgeClosed A D
    (x := ForgetEnrichment.of (Complex A) q) (y := ForgetEnrichment.of (Complex A) x) t
  refine ⟨q, s, ?_, h, hh⟩
  rw [hs]
  exact ht

end SerrePositivity.InfinityCategories
