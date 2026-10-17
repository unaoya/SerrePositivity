module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CosimplicialDegenerateHorn
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryCotensor

/-! # Any two degenerate whole horn families agree on their overlap

Transposition puts the whole external parameter into the target. The
cosimplicial uniqueness argument then applies in every dimension and
for every pair of degeneracies, without any Kan assumption.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.DegenerateHornOverlap
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2)) (j k : Fin (n + 1))
  {L : SSet.{v}} (a b : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)

lemma eq_of_same_horn
    (h : a ≫ DegenerateHornInput.boundary i j K = b ≫ DegenerateHornInput.boundary i k K) :
    a ≫ DegenerateHornInput.degeneracy j K = b ≫ DegenerateHornInput.degeneracy k K := by
  have ht := congrArg BoundaryCotensor.transpose h
  change BoundaryCotensor.transpose
      ((a ≫ (pre (SSet.stdSimplex.σ j)).app K) ≫ (pre (SSet.horn (n + 1) i).ι).app K) =
    BoundaryCotensor.transpose
      ((b ≫ (pre (SSet.stdSimplex.σ k)).app K) ≫ (pre (SSet.horn (n + 1) i).ι).app K) at ht
  simp only [BoundaryCotensor.transpose_restriction] at ht
  have hf : ∀ r : Fin (n + 2), r ≠ i →
      SSet.stdSimplex.δ r ≫ SSet.stdSimplex.σ j ≫ BoundaryCotensor.transpose a =
        SSet.stdSimplex.δ r ≫ SSet.stdSimplex.σ k ≫ BoundaryCotensor.transpose b := by
    intro r hr
    have he := congrArg (fun q => SSet.horn.ι i r hr ≫ q) ht
    simpa only [← Category.assoc, SSet.horn.ι_ι] using he
  apply BoundaryCotensor.transpose_injective
  change BoundaryCotensor.transpose (a ≫ (pre (SSet.stdSimplex.σ j)).app K) =
    BoundaryCotensor.transpose (b ≫ (pre (SSet.stdSimplex.σ k)).app K)
  rw [BoundaryCotensor.transpose_restriction, BoundaryCotensor.transpose_restriction]
  exact CosimplicialDegenerateHorn.eq_of_faces SSet.stdSimplex i j k
    (BoundaryCotensor.transpose a) (BoundaryCotensor.transpose b) hf

end SerrePositivity.SimplicialModel.DegenerateHornOverlap
