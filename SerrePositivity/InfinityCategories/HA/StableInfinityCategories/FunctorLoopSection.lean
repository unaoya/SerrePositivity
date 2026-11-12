module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopFamily

/-!
概要：元の実 loop 切断を関手圏の実 loop 切断へ持ち上げる。
方針：全評価での零角と引き戻し性を用いて全部分圏へ因子化する。
規約：元の loop 関手と切断の等式を厳密に保持する。
使われ方：関手区間の cofiber 族と回転の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：関手圏の四角形を点で評価すると元の同じ loop 四角形になる。
方針：全族の厳密評価式を関手頂点の全単射で読み戻す。
規約：四角形全体の等式。使われ方：loop の頂点条件。 -/
lemma functorLoopSquareFamily_vertex_evaluate {K X : SSet.{u}}
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (v : ((ihom K).obj X) _⦋0⦌) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s).app (Opposite.op ⦋0⦌) v) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((s.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌) v)).val) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  have hl := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) ((ihom K).obj X)).apply_symm_apply
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s).app (Opposite.op ⦋0⦌) v)
  have hr := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[1] ⊗ Δ[1] : SSet.{u}) X).apply_symm_apply
    ((s.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌) v)).val)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram _) = _ at hl hr
  calc
    _ = ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram
            ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s).app (Opposite.op ⦋0⦌) v))) := rfl
    _ = ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k)).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s).app (Opposite.op ⦋0⦌) v) :=
      congrArg _ hl
    _ = (s.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌) v)).val :=
      congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily_evaluate s k)
    _ = _ := hr.symm

/-- 概要：関手圏に送った loop 族の各頂点は実 loop 四角形である。
方針：全ての評価で元の零角と引き戻し性を検査する。
規約：標的の安定性は不要。使われ方：loop 図式の全部分圏への持ち上げ。 -/
lemma isLoopDiagramVertex_functorLoopSquareFamily {K X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X)
    (v : ((ihom K).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s).app (Opposite.op ⦋0⦌) v) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s).app (Opposite.op ⦋0⦌) v)
  have hk (k : K _⦋0⦌) := functorLoopSquareFamily_vertex_evaluate s v k
  have hd (k : K _⦋0⦌) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    (s.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌) v))
  refine ⟨?_, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_of_pointwise_evaluation
    intro k
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) 0 1)
    rw [hk k]
    exact (hd k).1
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isZeroVertex_of_pointwise_evaluation
    intro k
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) 1 0)
    rw [hk k]
    exact (hd k).2.1
  · apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functorCategory_iff_pointwise F).mpr
    intro k
    rw [hk k]
    exact (hd k).2.2

/-- 概要：元の全 loop 族を関手圏の実 loop 図式へ因子化する。
方針：点ごとの頂点条件から全部分圏へ持ち上げる。
規約：まだ切断の条件は使わない。使われ方：関手圏の native loop 入力。 -/
def functorLoopSection (K : SSet.{u}) {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) :
    (ihom K).obj X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams ((ihom K).obj X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily K s)
    (isLoopDiagramVertex_functorLoopSquareFamily s)

/-- 概要：関手圏の loop 図式の各角は元の同じ評価への後合成。
方針：全部分圏への持ち上げの厳密な包含等式を用いる。
規約：四つの角を同じ順序で評価する。
使われ方：切断の恒等式と loop 同値の保存。 -/
lemma functorLoopSection_evaluation {K X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (i j : Fin 2) :
    functorLoopSection K s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation ((ihom K).obj X) i j =
      (ihom K).map (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X i j) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation, functorLoopSection]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorLoopSquareFamily_corner s i j

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
