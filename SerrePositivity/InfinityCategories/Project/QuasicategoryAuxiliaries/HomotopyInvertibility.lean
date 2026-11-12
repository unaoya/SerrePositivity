module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.ArrowSquareHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass

/-! # 指定された端点の道とホモトピーの可逆性

概要：区間のホモトピーの可逆性を両端の指定した道で判定する。
方針：評価した関手辺と道の類を比較し、点ごとの可逆性の判定を使う。
規約：指定された辺を保つ。使われ方：cofiber 図式の同型比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：関手辺が可逆なホモトピーの各頂点上の辺は可逆。
方針：関手辺から戻したホモトピーと元の射を照合する。
規約：始域は任意、値域は quasicategory。使われ方：枝の比較から span の比較へ。 -/
lemma homotopyVertex_isInvertible_of_functorEdge {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (H : SSet.Homotopy F G)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).toTruncated := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible e hH k
  have hraw : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e).h = H.h := by
    change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
    rw [Equiv.symm_apply_apply, uncurry_curry]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e) k).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).edge :=
    congrArg (fun q => q.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj K) k).edge,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hraw
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).1 h

/-- 概要：指定頂点上の道が可逆なら、その頂点で評価した比較も同型。
方針：評価と端点を保持した自然変換の Arrow の等号を使う。
規約：道の両端の等号を輸送に含める。使われ方：区間の始点・終点での判定。 -/
lemma homotopyEvaluation_isIso_of_vertexPath {K X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ X} (H : SSet.Homotopy F G) (i : (Δ[0] : SSet.{u}) ⟶ K)
    {x y : X _⦋0⦌} (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a)
    (h : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge) :
    IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv i))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluationOfEndpoints_arrow H (SSet.yonedaEquiv i)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyNatTransOfEndpoints_vertexPath_arrow H i a h)
  exact (congrArg (fun q : Arrow (hoFunctor.obj X) => IsIso q.hom) he).mpr ha

/-- 概要：区間のホモトピーは二つの頂点での評価が同型なら可逆。
方針：区間の零単体を二つの端点に分類し、評価による可逆性判定を適用する。
規約：値域は quasicategory。使われ方：辺のホモトピーの可逆性。 -/
lemma arrowHomotopy_isInvertible_of_evaluations {X : SSet.{u}} [Quasicategory X]
    {f g : (Δ[1] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g)
    (h : ∀ i : Fin 2, IsIso ((hoFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm i))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt _).2
  intro x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  exact h i

/-- 概要：区間の両端で指定した道が可逆なら、ホモトピー全体も可逆。
方針：各端点での評価を指定した道の類と比較する。
規約：二つの道の一次単体を保つ。使われ方：cofiber 列の第一枝の比較。 -/
lemma arrowHomotopy_isInvertible_of_endpointPaths {X : SSet.{u}} [Quasicategory X]
    {f g : (Δ[1] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g)
    {x₀ y₀ x₁ y₁ : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x₀ y₀)
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X) x₁ y₁)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge b)
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge)
    (h₁ : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm b.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  apply arrowHomotopy_isInvertible_of_evaluations H
  intro i
  fin_cases i
  · have h := homotopyEvaluation_isIso_of_vertexPath H (stdSimplex.δ (1 : Fin 2)) a ha h₀
    have hv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    exact (congrArg (fun v : (Δ[1] : SSet.{u}) _⦋0⦌ =>
      IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))) hv).mp h
  · have h := homotopyEvaluation_isIso_of_vertexPath H (stdSimplex.δ (0 : Fin 2)) b hb h₁
    have hv : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
        stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
    exact (congrArg (fun v : (Δ[1] : SSet.{u}) _⦋0⦌ =>
      IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))) hv).mp h

/-- 概要：両方の終点が終対象で、始点の指定道が可逆なら区間のホモトピーは可逆。
方針：終点での比較は終対象間の射なので同型となる。
規約：値域は quasicategory。使われ方：cofiber 列の零角へ向かう第二枝。 -/
lemma arrowHomotopy_isInvertible_of_sourcePath_terminal_targets {X : SSet.{u}}
    [Quasicategory X] {f g : (Δ[1] : SSet.{u}) ⟶ X} (H : SSet.Homotopy f g)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (g.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    {x y : X _⦋0⦌} (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a)
    (h₀ : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm a.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H) := by
  apply arrowHomotopy_isInvertible_of_evaluations H
  intro i
  fin_cases i
  · have h := homotopyEvaluation_isIso_of_vertexPath H (stdSimplex.δ (1 : Fin 2)) a ha h₀
    have hv : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) =
        stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    exact (congrArg (fun v : (Δ[1] : SSet.{u}) _⦋0⦌ =>
      IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))) hv).mp h
  · have hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      exact hf
    have hg' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
      exact hg
    exact isIso_of_isTerminal hf'.isTerminalHo hg'.isTerminalHo _

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
