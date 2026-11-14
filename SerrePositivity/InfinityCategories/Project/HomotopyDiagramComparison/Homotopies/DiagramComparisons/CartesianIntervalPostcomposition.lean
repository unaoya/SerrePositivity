module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianOpposite

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.IntervalMappingOppositeComposition

/-!
概要：Cartesian 辺による後合成は、下段始域からの写像空間のホモトピー同値。
方針：反対の辺の coCartesian 性と、反転同型の標準の合成作用との整合を使う。
規約：底は標準区間、指定辺を保持。使われ方：Quillen 導来随伴の単位の各点の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 辺の両端と代表を保つ輸送は、標準の前合成の同値性を保つ。 -/
lemma intervalPrecompose_equivalence_transport {E : SSet.{u}} [Quasicategory E]
    {a b a' b' : E _⦋0⦌} (ha : a = a') (hb : b = b')
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) a b)
    (f' : SSet.Truncated.Edge (X := (truncation 2).obj E) a' b')
    (he : f.edge = f'.edge) (y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y (SSet.Truncated.HomotopyCategory.homMk f)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y (SSet.Truncated.HomotopyCategory.homMk f')) := by
  subst a' b'
  have h : f = f' := SSet.Truncated.Edge.ext he
  subst f'
  rfl

/-- 一次単体で指定した coCartesian 辺による標準の前合成は同値である。 -/
lemma intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesianEdge
    {E : SSet.{u}} [Quasicategory E] {a b : E _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) a b) (y : E _⦋0⦌)
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (hp : p.app (Opposite.op ⦋1⦌) f.edge = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p f.edge)
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y
      (SSet.Truncated.HomotopyCategory.homMk f)) := by
  rcases f with ⟨s, hs, ht⟩
  change E _⦋1⦌ at s
  change p.app (Opposite.op ⦋1⦌) s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge at hp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p s at hf
  change E.δ 1 s = a at hs
  change E.δ 0 s = b at ht
  subst a b
  let e : (Δ[1] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm s
  have hpe : e ≫ p = 𝟙 Δ[1] := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, hp]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hfe : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (SSet.yonedaEquiv e) := by
    simpa only [e, Equiv.apply_symm_apply] using hf
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesian e y p hpe hfe hy
  have hsrc : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e) = E.δ 1 s := by
    exact (stdSimplex.yonedaEquiv_δ_comp (n := 0) e 1).trans
      (congrArg (E.δ 1) (Equiv.apply_symm_apply _ s))
  have htgt : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e) = E.δ 0 s := by
    exact (stdSimplex.yonedaEquiv_δ_comp (n := 0) e 0).trans
      (congrArg (E.δ 0) (Equiv.apply_symm_apply _ s))
  exact (intervalPrecompose_equivalence_transport hsrc htgt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e)
    ⟨s, rfl, rfl⟩ (Equiv.apply_symm_apply _ s) y).mp h

/-- 元の Cartesian 辺による標準の後合成は、下段始域への写像空間上で同値である。 -/
lemma intervalPostcompose_isSimplicialHomotopyEquivalence_of_cartesian
    {E : SSet.{u}} [Quasicategory E] (e : (Δ[1] : SSet.{u}) ⟶ E) (x : E _⦋0⦌)
    (p : E ⟶ (Δ[1] : SSet.{u})) (hp : e ≫ p = 𝟙 Δ[1])
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p (SSet.yonedaEquiv e))
    (hx : p.app (Opposite.op ⦋0⦌) x = stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose x
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e))) := by
  let q : E.op ⟶ (Δ[1] : SSet.{u}) :=
    SSet.opFunctor.map p ≫ (stdSimplex.opIso ⦋1⦌).hom
  let f : SSet.Truncated.Edge (X := (truncation 2).obj E)
    (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e))
    (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.edgeCosliceEdge e
  have hq : q.app (Opposite.op ⦋1⦌) (SSet.opObjEquiv.symm (SSet.yonedaEquiv e)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    have h := congrArg SSet.yonedaEquiv hp
    rw [SSet.yonedaEquiv_comp] at h
    change (stdSimplex.opIso ⦋1⦌).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv e))) = _
    rw [h]
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hfc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (SSet.opObjEquiv.symm (SSet.yonedaEquiv e)) := by
    have hfo := he.op
    exact hfo.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration (stdSimplex.opIso ⦋1⦌).hom _)
  have hqx : q.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm x) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    change (stdSimplex.opIso ⦋1⦌).hom.app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm (p.app (Opposite.op ⦋0⦌) x)) = _
    rw [hx]
    rfl
  have hpre := intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesianEdge
    (E := E.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp (X := E) f) (SSet.opObjEquiv.symm x) q hq hfc hqx
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.intervalPostcompose_isSimplicialHomotopyEquivalence_of_op_precompose (E := E) x f hpre

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
