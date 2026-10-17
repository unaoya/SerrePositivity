module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NormalizedHornTargetComposition

/-! # Whole faces of the selected target composition triangle -/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedHornTargetFaces
variable {K L M : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L))
  (hM : SSet.modelCategoryQuillen.J.rlp (terminal.from M)) (q : K ⟶ L) (r : L ⟶ M)

lemma zero : _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
    ((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (NormalizedHornTargetComparison.comparison i hL hM r).h := by
  rw [NormalizedHornTargetComposition.triangle_face]
  exact NormalizedHornTargetComposition.second_h i hL hM q r

lemma one : _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
      (NormalizedHornTargetComparison.comparison i hK hM (q ≫ r)).h :=
  NormalizedHornTargetComposition.triangle_face i hK hL hM q r 1

lemma two : _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
    (NormalizedHornTargetComparison.comparison i hK hL q).h ≫
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map r := by
  rw [NormalizedHornTargetComposition.triangle_face]
  exact NormalizedHornTargetComposition.first_h i hK hL q r

end SerrePositivity.SimplicialModel.NormalizedHornTargetFaces
