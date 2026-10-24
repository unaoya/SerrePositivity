module

public import SerrePositivity.InfinityCategories.F1B.Diagrams.IntervalMaximum
public import SerrePositivity.InfinityCategories.Core.EquivalenceIntervalEdge
public import SerrePositivity.InfinityCategories.Core.EquivalencePathFinalLifting
public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：指定された可逆辺そのものを可逆区間全体へ延長する。
方針：最大値の正方形を終点固定の可逆 path の fiber へ送り、可縮性で延長する。
規約：端点だけでなく標準区間上の元の射を厳密に回収する。
使われ方：圏論的同値に対する右持ち上げから可逆辺の指定された持ち上げを得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可逆な標準区間からの射は、その射を保って可逆区間全体へ延長できる。
方針：指定辺から終点の恒等辺への最大値の正方形を可縮な可逆 path の fiber で延長する。
規約：X は quasicategory、元の辺のホモトピー類だけを回収するのではない。
使われ方：終点と像を厳密に固定した可逆辺の持ち上げ。 -/
lemma exists_kanEquivalenceInterval_extension_of_invertibleEdge {X : SSet.{u}}
    [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv e))) :
    ∃ F : equivalenceInterval ⟶ X, equivalenceIntervalEdge ≫ F = e := by
  let y := e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let H := SerrePositivity.InfinityCategories.F1B.intervalMaximum ≫ e
  have hv : ∀ t : (Δ[1] : SSet.{u}) _⦋0⦌,
      IsEquivalencePathVertex ((curry H).app (Opposite.op ⦋0⦌) t) := by
    intro t
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
    unfold IsEquivalencePathVertex
    rw [intervalFunctorVertexEdge_curry]
    fin_cases i
    · have hz : SerrePositivity.InfinityCategories.F1B.intervalMaximum.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
            PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 1) =
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by decide
      change IsInvertibleEdge (edgeOfSimplex (e.app _ (SerrePositivity.InfinityCategories.F1B.intervalMaximum.app _ _)))
      erw [hz]
      have hh := congrArg SSet.yonedaEquiv (Category.id_comp e)
      change e.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        SSet.yonedaEquiv e at hh
      exact (isInvertibleEdge_congr hh).2 he
    · have ho : SerrePositivity.InfinityCategories.F1B.intervalMaximum.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
            PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 1) =
        PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 1 := by decide
      change IsInvertibleEdge (edgeOfSimplex (e.app _ (SerrePositivity.InfinityCategories.F1B.intervalMaximum.app _ _)))
      erw [ho, pinchedConstant_map]
      have hi := isEquivalencePathVertex_const y
      rw [IsEquivalencePathVertex, intervalFunctorVertexEdge_functorVertex] at hi
      exact hi
  let v : (Δ[1] : SSet.{u}) ⟶ equivalencePath X :=
    fullSubcomplexLift IsEquivalencePathVertex (curry H) hv
  have hvi : v ≫ equivalencePathι X = curry H := fullSubcomplexLift_ι _ _ _
  have hvq : v ≫ equivalencePathEndpoint X 1 = SSet.const y := by
    change (v ≫ equivalencePathι X) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = _
    rw [hvi, curry_evaluateFunctorAt_interval]
    change prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (SerrePositivity.InfinityCategories.F1B.intervalMaximum ≫ e) = SSet.const y
    rw [← Category.assoc, SerrePositivity.InfinityCategories.F1B.intervalMaximum_first_one, SSet.const_comp]
  let p := equivalencePathEndpoint X 1
  let a := vertexFiberLift p y v hvq
  have hc := vertexFiber_isContractibleKan p y
  have := (isContractibleKan_iff_trivialKanFibration _).mp hc
  have := TrivialKanFibration.mem (p := terminal.from (vertexFiber p y))
    equivalenceIntervalEdge inferInstance
  let sq : CommSq a equivalenceIntervalEdge (terminal.from (vertexFiber p y))
      (terminal.from equivalenceInterval) := ⟨terminal.hom_ext _ _⟩
  refine ⟨sq.lift ≫ vertexFiberι p y ≫ equivalencePathEndpoint X 0, ?_⟩
  rw [← Category.assoc, sq.fac_left, ← Category.assoc, vertexFiberLift_ι]
  change (v ≫ equivalencePathι X) ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = e
  rw [hvi, curry_evaluateFunctorAt_interval]
  change prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ (SerrePositivity.InfinityCategories.F1B.intervalMaximum ≫ e) = e
  rw [← Category.assoc, SerrePositivity.InfinityCategories.F1B.intervalMaximum_first_zero, Category.id_comp]

end SerrePositivity.InfinityCategories.F1B
