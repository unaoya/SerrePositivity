module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass

/-!
概要：区間全比較の同じ端点経路から、評価した射の類の一致を回収する。
方針：指定端点を同じ一次単体で評価し、既存のホモトピー評価式へ運ぶ。
規約：元全ホモトピーを保持。使われ方：共有零対角上の全比較一意性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories
open scoped Simplicial

/-- 概要：同じ頂点経路の全一単体を持つ二ホモトピーの評価した射の類は等しい。
方針：元ホモトピー評価の Arrow 表示と同じ辺の類の一致を使う。
規約：元二比較を保持。使われ方：零対角全比較の二端点照合。 -/
lemma homotopyEvaluation_eq_of_vertexEdge {A X : SSet.{u}} {F G : A ⟶ X}
    (H J : SSet.Homotopy F G) (x : A _⦋0⦌)
    (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge J x).edge) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) := by
  let a := (SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge
  let e := a.map ((truncation 2).map H.h)
  let e' := a.map ((truncation 2).map J.h)
  have he : e.edge = e'.edge := h
  have hH := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow H x
  have hJ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow J x
  change Arrow.mk _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e) at hH
  change Arrow.mk _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e') at hJ
  apply Arrow.mk_injective
  exact hH.trans ((SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk e e' he).trans hJ.symm)

/-- 概要：元区間二比較の同じ端点側面は評価した射の類の一致を与える。
方針：標準零単体上の恒等辺と時刻辺で同じ側面を評価する。
規約：端点の全経路を使用。使われ方：上下共有対角の評価した両端の一致。 -/
lemma homotopyEvaluation_eq_of_endpoint {X : SSet.{u}}
    {F G : (Δ[1] : SSet.{u}) ⟶ X} (H J : SSet.Homotopy F G) (i : Fin 2)
    (h : (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ J.h) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv (stdSimplex.δ i)))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (SSet.yonedaEquiv (stdSimplex.δ i)))).toFunctor.map
        (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy J)) := by
  apply homotopyEvaluation_eq_of_vertexEdge
  let z : (Δ[0] ⊗ Δ[1] : SSet.{u}) _⦋1⦌ :=
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
  have he := congrArg (fun q : (Δ[0] ⊗ Δ[1] : SSet.{u}) ⟶ X => q.app (Opposite.op ⦋1⦌) z) h
  have hv : (stdSimplex.δ i).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      SSet.yonedaEquiv (stdSimplex.δ i) := by
    apply stdSimplex.obj₀Equiv.injective
    fin_cases i <;> rfl
  have hid : (stdSimplex.δ i).app (Opposite.op ⦋1⦌)
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
        (stdSimplex.obj₀Equiv.symm 0)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[1] : SSet.{u}))
        (SSet.yonedaEquiv (stdSimplex.δ i))).edge := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (stdSimplex.δ i) (stdSimplex.obj₀Equiv.symm 0) 1).trans
      (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) hv)
  change H.h.app (Opposite.op ⦋1⦌)
      ((stdSimplex.δ i).app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm 0)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
    J.h.app (Opposite.op ⦋1⦌)
      ((stdSimplex.δ i).app (Opposite.op ⦋1⦌)
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
          (stdSimplex.obj₀Equiv.symm 0)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) at he
  rw [hid] at he
  exact he
end SerrePositivity.KST.SConstruction
