module
public import SerrePositivity.PerfectComplex.KoszulClasses

public import SerrePositivity.KTheory.Adams.UnitNormalization
public import SerrePositivity.KTheory.Adams.SupportNaturality

/-! # Normalization on finite Koszul sequences -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

variable [Invertible (2 : R)]

lemma tensorSquareClass_koszul_zero (x : Fin 0 → R) :
    tensorSquareClass (koszulComplex x) (koszulClosedSupport x)
      (isPerfectSupported_koszulComplex x).strictlyPerfect (koszulComplex_closedSupport x) =
    koszulClass x := by
  unfold koszulClass
  exact tensorSquareClass_unit_on (koszulClosedSupport x) (koszulComplex_closedSupport x)

/-- Axiom A4 for every finite Koszul sequence, including the empty sequence. -/
lemma cyclicTwo_koszul {n : ℕ} (x : Fin n → R) :
    cyclicTwo (koszulClosedSupport x) (koszulClass x) = (2 : ℤ) ^ n • koszulClass x := by
  induction n with
  | zero =>
    rw [pow_zero, one_smul]
    exact
      (cyclicTwo_mk_concrete (koszulClosedSupport x) (koszulComplex x)
        (isPerfectSupported_koszulComplex x).strictlyPerfect (koszulComplex_closedSupport x)).trans
          (tensorSquareClass_koszul_zero x)
  | succ n ih =>
    rw [koszulClass_succ x, cyclicTwo_enlarge, cyclicTwo_cup,
      cyclicTwo_oneKoszul, ih (Fin.init x)]
    simp only [map_zsmul, AddMonoidHom.smul_apply, smul_smul, pow_succ]

end Adams
end SerrePositivity
