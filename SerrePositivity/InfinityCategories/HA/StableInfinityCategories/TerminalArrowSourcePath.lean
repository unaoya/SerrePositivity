module
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalBoundaryEdgeLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TerminalArrowRelative

/-! # 指定した始点の道を持つ終対象への辺の比較

概要：終対象への辺へのホモトピーを、始点の道を厳密に指定して構成する。
方針：関手圏の始点評価の相対終点境界充填で辺を持ち上げる。
規約：始点の道を恒等射に固定しない。
使われ方：S4 の TR3 の零角を持つ span の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：終対象を終点とする辺への比較は任意の指定始点の道を持つように選べる。
方針：始点評価の終点での相対境界充填により関手辺を持ち上げ、uncurry する。
規約：入力の辺と始点の道の一次単体を保持する。使われ方：TR3 の第二の枝。 -/
lemma exists_terminalArrowHomotopy_of_sourcePath {X : SSet.{u}} [Quasicategory X]
    (f g : (Δ[1] : SSet.{u}) ⟶ X)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) :
    ∃ H : SSet.Homotopy f g,
      (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have hf₀ : p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ f
  have hg₀ : p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) =
      g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ g
  let a' : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
      (p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) := {
    edge := a.edge
    src_eq := a.src_eq.trans hf₀.symm
    tgt_eq := a.tgt_eq.trans hg₀.symm }
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_edge_lift_of_terminalBoundaryLifting p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.terminalBoundaryLifting_arrowSource_of_terminalTarget g hg) a'
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e
  have hp : SSet.yonedaEquiv.symm e.edge ≫ p = SSet.yonedaEquiv.symm a.edge := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    have h := congrArg SSet.Truncated.Edge.edge he
    exact h.trans (SSet.yonedaEquiv.apply_symm_apply a.edge).symm
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ H.h = SSet.yonedaEquiv.symm a.edge := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ uncurry (SSet.yonedaEquiv.symm e.edge) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    exact hp
  refine ⟨H, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.stableArrowEndpointCylinder]
  change (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})) ≫ H.h = _
  rw [Category.assoc, hs]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
