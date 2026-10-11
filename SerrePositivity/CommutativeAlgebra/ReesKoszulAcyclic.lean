module

public import SerrePositivity.CommutativeAlgebra.GradedAdicExactness
public import SerrePositivity.CommutativeAlgebra.GradedReesKoszulVanishing

/-! # Eventual acyclicity of the actual filtered Koszul tail

Evaluation at `t = 1` identifies each Rees coefficient grade with the
corresponding adic power in the original Koszul term. The uniform homogeneous
boundary bound therefore supplies exactness in every degree of a deep adic tail.
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.ReesKoszulAcyclic

open CategoryTheory CategoryTheory.Limits Filter ReesKoszulEvaluation

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Ideal R)
variable {h : ℕ} (z : Fin h → R) (hz : Ideal.span (Set.range z) = I)

include hz

/-- The actual Koszul differential has coefficients in the parameter ideal. -/
theorem differential_range_le :
    ∀ q, ((koszulComplex z).d q (q + 1)).hom.range ≤ I • ⊤ :=
  GradedAdicExactness.differential_range_le (sourceTermGrade R I z hz)
    (evaluationChainMapR R I z hz) I (map_sourceTermGrade R I z hz)
    (sourceTermGrade_differential R I z hz)

/-- The actual shifted adic Koszul tail is acyclic for all sufficiently large indices. -/
theorem eventually_adicTail_acyclic [IsNoetherianRing R] :
    ∀ᶠ n : ℕ in atTop, ∀ q,
      IsZero ((AdicFilteredComplex.tail (koszulComplex z) I
        (differential_range_le R I z hz) (n : ℤ)).homology q) := by
  obtain ⟨b, _, hbound⟩ := exists_uniform_bound_source_boundary R I z hz
  apply eventually_atTop.mpr
  refine ⟨b + h + 1, fun n hn => ?_⟩
  exact GradedAdicExactness.tail_acyclic_of_graded_boundary_lifting
    (sourceTermGrade R I z hz) (evaluationChainMapR R I z hz) I
    (map_sourceTermGrade R I z hz) (injOn_sourceTermGrade R I z hz)
    (sourceTermGrade_differential R I z hz) b h
    (fun q hq => hq.elim (koszulComplex_isZero_X_of_lt z q) (koszulComplex_isZero_X_of_pos z q))
    (fun q k hk _ => hbound q k hk) n hn

end SerrePositivity.ReesKoszulAcyclic
