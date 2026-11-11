module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroReturnTriangle

/-! # 終対象への合成二単体

概要：指定辺を、指定した終対象を最後の頂点とする二単体に延長する。
方針：終対象への二辺を選び、ホモトピー圏の射の一意性を合成二単体へ持ち上げる。
規約：最初の辺を厳密に保持。使われ方：任意の押し出しへの零対象の付加。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定辺は指定終対象を最後の頂点とする二単体に延長できる。
方針：終対象への二辺の合成の等号を実際の合成三角形で表す。
規約：安定性は不要。使われ方：零対象へ向かう押し出し長方形の下辺。 -/
lemma exists_terminalCompositeTriangle {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex z)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    ∃ τ : (Δ[2] : SSet.{u}) ⟶ X,
      stdSimplex.δ (2 : Fin 3) ≫ τ = SSet.yonedaEquiv.symm f.edge ∧
      τ.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) = z := by
  let g := Classical.choice (hz.nonempty_edge y)
  let e := Classical.choice (hz.nonempty_edge x)
  have h : SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g = SSet.Truncated.HomotopyCategory.homMk e :=
    hz.isTerminalHo.hom_ext _ _
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac h
  refine ⟨SSet.yonedaEquiv.symm t.simplex, ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₂.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm)
  · have he : stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
        SSet.yonedaEquiv.symm g.edge := by
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp]
      exact (congrArg (fun a => X.δ 0 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
        (t.d₀.trans (SSet.yonedaEquiv.apply_symm_apply g.edge).symm)
    have htgt := congrArg (fun q : (Δ[1] : SSet.{u}) ⟶ X =>
      X.δ 0 (SSet.yonedaEquiv q)) he
    have hv : X.δ 0 (SSet.yonedaEquiv
        (stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex)) =
        (SSet.yonedaEquiv.symm t.simplex).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) := by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, SSet.yonedaEquiv_comp]
      apply congrArg (fun s => (SSet.yonedaEquiv.symm t.simplex).app (Opposite.op ⦋0⦌) s)
      decide
    exact hv.symm.trans (htgt.trans
      ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.tgt_eq))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
