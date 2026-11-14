module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientRelativePrimitives
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRelativePrimitiveRefinement

/-! # 指定された有限個の商の原始元の共通実分母による相対持ち上げ

概要：互いに異なる次数の指定原始元を、一つの元の実分母と各比較境界で持ち上げる。
方針：有限族の帰納で閉分母を順に細分し、既存の両微分式を厳密に前合成して保つ。
規約：全入力の原始元を固定する。使われ方：pinched 境界の有限個の斉次成分の同時充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定された有限個の商の原始元に、共通実分母と元の原始元および比較境界が存在。 -/
theorem dgQuotientFinite_exists_relativePrimitives (P : Set D) (hP : localKFlat A D P)
    {m : ℕ} (x : D) (y : Fin m → D) (k : Fin m → ℤ)
    (a : ∀ i, GradedHom A x (y i) (k i + 1)) (ha : ∀ i, differential A (a i) = 0)
    (c : ∀ i, GradedHom A ((inclusion A D P).obj x) ((inclusion A D P).obj (y i)) (k i))
    (hc : ∀ i, differential A (c i) = ((inclusion A D P).map x (y i)).f (k i + 1) (a i)) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∀ i, ∃ h : GradedHom A q (y i) (k i),
        differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k i + 1) (a i) s ∧
        ∃ b : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj (y i)) (k i - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj (y i))).d (k i - 1) (k i) b =
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P) (k i) (c i) h s := by
  let F := inclusion A D P
  induction m generalizing x with
  | zero =>
    refine ⟨x, 𝟙 _, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_id A D P x, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ m ih =>
    obtain ⟨q, s, hs, hw⟩ := ih x (fun i => y i.succ) (fun i => k i.succ)
      (fun i => a i.succ) (fun i => ha i.succ) (fun i => c i.succ) (fun i => hc i.succ)
    let a0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k 0 + 1) (a 0) s
    let c0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A (QuotientObject D P)
      (q := F.obj q) (x := F.obj x) (y := F.obj (y 0)) (k 0) (c 0) (F.onClosed.map s)
    have ha0 : differential A a0 = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_closed A D (k 0 + 1) (a 0) (ha 0) s
    have hc0 : differential A c0 = (F.map q (y 0)).f (k 0 + 1) a0 := by
      have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_d A (QuotientObject D P)
        (q := F.obj q) (x := F.obj x) (y := F.obj (y 0)) (k 0) (k 0 + 1) rfl (c 0)
        (F.onClosed.map s)
      change differential A c0 = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A (QuotientObject D P)
        (q := F.obj q) (x := F.obj x) (y := F.obj (y 0)) (k 0 + 1)
          (differential A (c 0)) (F.onClosed.map s) at hd
      rw [hc 0] at hd
      exact hd.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorGradedPrecompose_map A D (QuotientObject D P) F
        (k 0 + 1) (a 0) s).symm
    obtain ⟨p, r, hr, h0, hh0, b0, hb0⟩ :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotient_exists_relativePrimitive A D P hP q (y 0) (k 0) a0 ha0 c0 hc0
    refine ⟨p, r ≫ s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P r s hr hs, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨h0, hh0.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp A D (k 0 + 1) (a 0) r s), b0,
        hb0.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual_nested A D (QuotientObject D P) F (k 0) (c 0) h0 r s)⟩
    · obtain ⟨h, hh, b, hb⟩ := hw j
      have hv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativePrimitiveWitness_refine A D (QuotientObject D P) F
        (p := p) (q := q) (x := x) (y := y j.succ) (k j.succ) (a j.succ) (c j.succ)
        h b r s hh hb
      exact ⟨_, hv.1, _, hv.2⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
