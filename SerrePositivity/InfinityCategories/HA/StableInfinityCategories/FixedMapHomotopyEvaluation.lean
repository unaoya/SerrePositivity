module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HomotopyEvaluationClass

/-! # 部分図式を固定するホモトピーの評価

概要：部分図式上で定値なホモトピーは、その全頂点で h の恒等成分を持つ。
方針：固定条件を退化した頂点と区間の一次単体で評価する。
規約：quasicategory 性は不要。使われ方：D7 の上三角形を固定した正方形比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 部分図式を固定するホモトピーは、その像の各頂点で恒等成分を与える。 -/
lemma homotopyEvaluation_fixed_map_arrow {A B X : SSet.{u}} {F G : B ⟶ X}
    (H : SSet.Homotopy F G) (i : A ⟶ B)
    (hfix : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst A Δ[1] ≫ i ≫ F) (a : A _⦋0⦌) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) (i.app (Opposite.op ⦋0⦌) a))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))) =
      Arrow.mk (𝟙 (SSet.HomotopyCategory.mk (F.app (Opposite.op ⦋0⦌)
        (i.app (Opposite.op ⦋0⦌) a)))) := by
  have he := congrArg (fun h : A ⊗ (Δ[1] : SSet.{u}) ⟶ X =>
    h.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hfix
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      F.app (Opposite.op ⦋1⦌) (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1)) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map] at he
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.homotopyEvaluation_arrow H (i.app (Opposite.op ⦋0⦌) a)).trans ?_
  let e := ((SSet.Truncated.Edge.id (X := (truncation 2).obj B)
    (i.app (Opposite.op ⦋0⦌) a)).tensor _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map ((truncation 2).map H.h)
  have heq : e.edge = (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
      (F.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) a))).edge := by
    change H.h.app (Opposite.op ⦋1⦌)
      ((SSet.Truncated.Edge.id (X := (truncation 2).obj B)
        (i.app (Opposite.op ⦋0⦌) a)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]
    exact he
  change Arrow.mk (SSet.Truncated.HomotopyCategory.homMk e) = _
  exact (SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk e
    (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
      (F.app (Opposite.op ⦋0⦌) (i.app (Opposite.op ⦋0⦌) a))) heq).trans
        (congrArg Arrow.mk (SSet.Truncated.HomotopyCategory.homMk_id _))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
