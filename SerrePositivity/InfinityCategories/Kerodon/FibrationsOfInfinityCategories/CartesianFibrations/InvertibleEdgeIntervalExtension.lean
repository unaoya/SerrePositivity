module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.IntervalMaximum
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceIntervalEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathFinalLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber

/-!
概要：指定された可逆辺そのものを可逆区間全体へ延長する。
方針：最大値の正方形を終点固定の可逆 path の fiber へ送り、可縮性で延長する。
規約：端点だけでなく標準区間上の元の射を厳密に回収する。
使われ方：圏論的同値に対する右持ち上げから可逆辺の指定された持ち上げを得る。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：可逆な標準区間からの射は、その射を保って可逆区間全体へ延長できる。
方針：指定辺から終点の恒等辺への最大値の正方形を可縮な可逆 path の fiber で延長する。
規約：X は quasicategory、元の辺のホモトピー類だけを回収するのではない。
使われ方：終点と像を厳密に固定した可逆辺の持ち上げ。 -/
lemma exists_kanEquivalenceInterval_extension_of_invertibleEdge {X : SSet.{u}}
    [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv e))) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge ≫ F = e := by
  let y := e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum ≫ e
  have hv : ∀ t : (Δ[1] : SSet.{u}) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((curry H).app (Opposite.op ⦋0⦌) t) := by
    intro t
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
    fin_cases i
    · have hz : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 1) =
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by decide
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (e.app _ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum.app _ _)))
      erw [hz]
      have hh := congrArg SSet.yonedaEquiv (Category.id_comp e)
      change e.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        SSet.yonedaEquiv e at hh
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hh).2 he
    · have ho : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum.app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})),
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 1) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 1 := by decide
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (e.app _ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum.app _ _)))
      erw [ho, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
      have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const y
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
      exact hi
  let v : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (curry H) hv
  have hvi : v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X = curry H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hvq : v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = SSet.const y := by
    change (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = _
    rw [hvi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum ≫ e) = SSet.const y
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_first_one, SSet.const_comp]
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p y v hvq
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan p y
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).mp hc
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y))
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge inferInstance
  let sq : CommSq a _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalEdge (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p y))
      (terminal.from _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) := ⟨terminal.hom_ext _ _⟩
  refine ⟨sq.lift ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0, ?_⟩
  rw [← Category.assoc, sq.fac_left, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  change (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = e
  rw [hvi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum ≫ e) = e
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.intervalMaximum_first_zero, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
