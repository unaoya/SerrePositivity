module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RightFibrationEdgeTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection

/-!
概要：右 fibration に沿い、指定した可逆辺そのものを始端固定で持ち上げる。
方針：逆辺を終端固定で持ち上げ、元の逆三角形を右ホーンで持ち上げる。
規約：射影は元の一次単体に厳密一致する。逆の取り直しによる同値類で済ませない。
使われ方：共通 BF 左脚を保持した実 loop 錐の前向き移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定可逆辺の同じ単体を、右 fibration の指定始端から持ち上げる。 -/
lemma d3_rightFibration_liftEdge_source {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (x : E _⦋0⦌) {y : B _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) x) y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ E,
      stdSimplex.δ 1 ≫ F = SSet.yonedaEquiv.symm x ∧
        F ≫ p = SSet.yonedaEquiv.symm e.edge := by
  obtain ⟨f, t, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge.nonempty_inverse he
  obtain ⟨G, hG₀, hGp⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.rightFibration_liftEdge_target p x f
  let z := E.δ 1 (SSet.yonedaEquiv G)
  let g : Truncated.Edge (X := (truncation 2).obj E) z x :=
    ⟨SSet.yonedaEquiv G, rfl, by
      change E.δ 0 (SSet.yonedaEquiv G) = x
      rw [← stdSimplex.yonedaEquiv_δ_comp, hG₀, Equiv.apply_symm_apply]⟩
  have hgp : (g.map ((truncation 2).map p)).edge = f.edge := by
    change p.app _ (SSet.yonedaEquiv G) = _
    rw [← SSet.yonedaEquiv_comp, hGp]
    exact SSet.yonedaEquiv.apply_symm_apply f.edge
  have hz : p.app (Opposite.op ⦋0⦌) z = y := by
    have hn := ConcreteCategory.congr_hom
      (p.naturality (SimplexCategory.δ (1 : Fin 2)).op) (SSet.yonedaEquiv G)
    exact hn.trans ((congrArg (fun a ↦ B.δ 1 a) hgp).trans f.src_eq)
  let e' : Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) z) :=
    ⟨e.edge, e.src_eq, e.tgt_eq.trans hz.symm⟩
  have t' : Truncated.Edge.CompStruct e' (g.map ((truncation 2).map p))
      ((Truncated.Edge.id (X := (truncation 2).obj E) x).map
        ((truncation 2).map p)) := by
    refine ⟨t.simplex, t.d₂, ?_, ?_⟩
    · exact t.d₀.trans hgp.symm
    · change B.δ 1 t.simplex = p.app _ (E.σ 0 x)
      calc
        _ = B.σ 0 (p.app (Opposite.op ⦋0⦌) x) := t.d₁
        _ = _ := (ConcreteCategory.congr_hom
          (p.naturality (SimplexCategory.σ (0 : Fin 1)).op) x).symm
  obtain ⟨a, s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_liftCompStruct p g
    (Truncated.Edge.id (X := (truncation 2).obj E) x) e' t'
  have hap : p.app (Opposite.op ⦋1⦌) a.edge = e.edge := by
    rw [← s.d₂]
    calc
      _ = B.δ 2 (p.app (Opposite.op ⦋2⦌) s.simplex) :=
        ConcreteCategory.congr_hom (p.naturality (SimplexCategory.δ (2 : Fin 3)).op)
          s.simplex
      _ = e.edge := by rw [hs]; exact t'.d₂
  refine ⟨SSet.yonedaEquiv.symm a.edge, ?_, ?_⟩
  · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (show E.δ 1 a.edge = x from a.src_eq)
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hap.trans (SSet.yonedaEquiv.apply_symm_apply e.edge).symm

end SerrePositivity.InfinityCategories
