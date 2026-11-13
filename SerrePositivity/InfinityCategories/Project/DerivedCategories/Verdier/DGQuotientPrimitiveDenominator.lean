module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientFiniteBoundaryCancellation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGGradedClosedPrecomposition

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商に原始元を持つ元の閉元に、閉実分母と同じ次数の元の原始元が存在する。 -/
theorem dgQuotientBoundary_exists_closedPrimitive (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y (k + 1)) (ha : _root_.SerrePositivity.DifferentialGraded.differential A a = 0)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) k)
    (hc : _root_.SerrePositivity.DifferentialGraded.differential A c = ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map x y).f (k + 1) a) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y k,
        differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a s := by
  have hk : k + 1 - 1 = k := by omega
  have hb (i : Fin 1) : ∃ b : _root_.SerrePositivity.DifferentialGraded.GradedHom A ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) (k + 1 - 1),
      (_root_.SerrePositivity.DifferentialGraded.homObject A (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D P) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)).d (k + 1 - 1) (k + 1) b =
          ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).map x y).f (k + 1) a := by
    rw [hk]
    exact ⟨c, hc⟩
  obtain ⟨q, t, ht, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFiniteBoundary_exists_primitives A D P hP
    x (fun _ : Fin 1 => y) (fun _ => k + 1) (fun _ => a) (fun _ => ha) hb
  have h0 := hp 0
  change (∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A q y (k + 1 - 1),
    (_root_.SerrePositivity.DifferentialGraded.homObject A D q y).d (k + 1 - 1) (k + 1) h =
      _root_.SerrePositivity.DifferentialGraded.compose A (D := D) (x := q) (y := x) (z := y) a
        (closedHomEquiv A D _ _ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed t)).val (zero_add (k + 1))) at h0
  rw [hk] at h0
  obtain ⟨h, hh⟩ := h0
  let s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed t
  have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s = t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_edgeClosed A D
    (x := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) (y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) t
  refine ⟨q, s, ?_, h, hh⟩
  rw [hs]
  exact ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories
