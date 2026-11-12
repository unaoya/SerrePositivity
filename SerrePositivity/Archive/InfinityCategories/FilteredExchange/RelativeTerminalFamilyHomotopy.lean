module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorRelativeTerminal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：相対終対象の族への比較円柱を元の底の上で厳密に構成する。
方針：関手空間の固定底 fiber の終対象へ辺を選び、元の円柱へ読み戻す。
規約：底は全時刻で定値。使われ方：部分形状の極限錐への元の錐族からの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対終点境界充填を持つ族へ、元の底を全時刻で保つ比較ホモトピーが存在。 -/
lemma exists_homotopy_to_relativeTerminal_family {A E D : SSet.{u}}
    (p : E ⟶ D) (f g : A ⟶ E) (hfg : f ≫ p = g ≫ p)
    (hg : ∀ a : A _⦋0⦌, TerminalBoundaryLifting p (g.app (Opposite.op ⦋0⦌) a)) :
    ∃ H : SSet.Homotopy f g, H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
  let r := (ihom A).map p
  let b := functorVertex (f ≫ p)
  let s : (vertexFiber r b) _⦋0⦌ := ⟨functorVertex f, by
    change functorVertex (f ≫ p) = PinchedHom.constant b 0
    rw [pinchedConstant_zero]⟩
  let t : (vertexFiber r b) _⦋0⦌ := ⟨functorVertex g, by
    change functorVertex (g ≫ p) = PinchedHom.constant b 0
    rw [pinchedConstant_zero, ← hfg]⟩
  have ht : TerminalBoundaryLifting r t.val :=
    terminalBoundaryLifting_ihom_of_pointwise p g hg
  have hterm := TerminalBoundaryLifting.isTerminalVertex_fiber r b t ht
  obtain ⟨e₀⟩ := hterm.nonempty_edge s
  let e := e₀.map ((truncation 2).map (vertexFiberι r b))
  let H := simplicialHomotopyOfFunctorEdge e
  have hp : SSet.yonedaEquiv.symm e.edge ≫ r = SSet.const b := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change r.app (Opposite.op ⦋1⦌) e₀.edge.val = PinchedHom.constant b 1
    exact e₀.edge.property
  refine ⟨H, ?_⟩
  change uncurry (SSet.yonedaEquiv.symm e.edge) ≫ p = _
  rw [← uncurry_natural_right]
  change uncurry (SSet.yonedaEquiv.symm e.edge ≫ r) = _
  rw [hp]
  exact uncurry_const_functorVertex (f ≫ p)

end SerrePositivity.InfinityCategories.F2
