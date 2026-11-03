module
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.PinchedHom.Basic
public import SerrePositivity.InfinityCategories.Core.HomotopyEvaluationClass

/-! # 頂点上の道によるホモトピー成分の計算

概要：ホモトピーの頂点上の制限が指定した道なら、その評価した h の射は道の類である。
方針：制限の式を一次単体で評価し、成分の辺を比較する。
規約：端点の輸送は Arrow の等号に含める。
使われ方：S4 の水平変形の始点成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：頂点上のホモトピーが指定した道なら評価した類はその道の類である。
方針：制限の一次単体を評価して、自然変換の成分の辺と同じ単体を持つことを示す。
規約：quasicategory 性は不要。使われ方：水平変形の始点成分の計算。 -/
lemma homotopyEvaluation_arrow_of_vertexPath {A X : SSet.{u}} {F G : A ⟶ X}
    (H : SSet.Homotopy F G) (i : (Δ[0] : SSet.{u}) ⟶ A) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (h : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = snd Δ[0] Δ[1] ≫ g) :
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := X) (SSet.yonedaEquiv i))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))) =
        Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex (SSet.yonedaEquiv g))) := by
  let a := stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 1)
  have hia : i.app (Opposite.op ⦋0⦌) a = SSet.yonedaEquiv i := by
    have ha : a = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [ha, ← SSet.yonedaEquiv_comp, Category.id_comp]
  have he := congrArg (fun q : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ X ↦
    q.app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1, homotopyIntervalEdge.edge)) h
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (PinchedHom.constant a 1), homotopyIntervalEdge.edge) =
      g.app (Opposite.op ⦋1⦌) homotopyIntervalEdge.edge at he
  rw [pinchedConstant_map, hia] at he
  have hi : homotopyIntervalEdge.{u}.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  rw [hi, ← SSet.yonedaEquiv_comp, Category.id_comp] at he
  let e := ((SSet.Truncated.Edge.id (X := (truncation 2).obj A)
    (SSet.yonedaEquiv i)).tensor homotopyIntervalEdge).map ((truncation 2).map H.h)
  have heq : e.edge = (edgeOfSimplex (SSet.yonedaEquiv g)).edge := by
    change H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) (SSet.yonedaEquiv i)).edge,
        homotopyIntervalEdge.edge) = SSet.yonedaEquiv g
    rw [← pinchedConstant_one, hi]
    exact he
  exact (homotopyEvaluation_arrow H (SSet.yonedaEquiv i)).trans
    (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk e _ heq)

end SerrePositivity.InfinityCategories
