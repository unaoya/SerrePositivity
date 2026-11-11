module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativeTrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-! 実 prism の二端と基底全体を保つ二次元の比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

lemma dgGluingRelativePrismHomotopy_exists {K E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (F G : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ G)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ F = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ G)
    (hp : F ≫ p = G ≫ p) :
    ∃ H : SSet.Homotopy F G,
      (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst ((boundary 1 : SSet.{u}) ⊗ K) (Δ[1] : SSet.{u}) ≫
          ((boundary 1).ι ▷ K) ≫ G ∧
      H.h ≫ p = fst ((Δ[1] : SSet.{u}) ⊗ K) (Δ[1] : SSet.{u}) ≫ G ≫ p := by
  have : Mono ((boundary 1).ι ▷ K) := (tensorRight K).map_mono _
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativeHomotopy_of_trivialFibration_exists ((boundary 1).ι ▷ K) p F G _ hp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict F, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram_restrict G, h₀, h₁]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
