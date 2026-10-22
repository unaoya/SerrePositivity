module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativeTrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.Core.IntervalBoundary

/-! 実 prism の二端と基底全体を保つ二次元の比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

lemma dgGluingRelativePrismHomotopy_exists {K E B : SSet.{u}}
    (p : E ⟶ B) [TrivialKanFibration p] (F G : (Δ[1] : SSet.{u}) ⊗ K ⟶ E)
    (h₀ : prismEndpoint 0 K ≫ F = prismEndpoint 0 K ≫ G)
    (h₁ : prismEndpoint 1 K ≫ F = prismEndpoint 1 K ≫ G)
    (hp : F ≫ p = G ≫ p) :
    ∃ H : SSet.Homotopy F G,
      (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst ((boundary 1 : SSet.{u}) ⊗ K) (Δ[1] : SSet.{u}) ≫
          ((boundary 1).ι ▷ K) ≫ G ∧
      H.h ≫ p = fst ((Δ[1] : SSet.{u}) ⊗ K) (Δ[1] : SSet.{u}) ≫ G ≫ p := by
  have : Mono ((boundary 1).ι ▷ K) := (tensorRight K).map_mono _
  apply dgGluingRelativeHomotopy_of_trivialFibration_exists ((boundary 1).ι ▷ K) p F G _ hp
  rw [intervalBoundaryDiagram_restrict F, intervalBoundaryDiagram_restrict G, h₀, h₁]

end SerrePositivity.InfinityCategories
