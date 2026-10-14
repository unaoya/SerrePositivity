module

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

lemma koszulClosedSupport_zero (x : Fin 0 → R) :
    koszulClosedSupport x = (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) := by
  apply SetLike.coe_injective
  ext p
  simp [koszulClosedSupport]

def koszulClass {n : ℕ} (x : Fin n → R) : K0WithSupport (koszulClosedSupport x) :=
  K0WithSupport.mk (koszulClosedSupport x) (supportedPerfectOnObj (koszulClosedSupport x)
    (koszulComplex x) (isPerfectSupported_koszulComplex x).strictlyPerfect
    (koszulComplex_closedSupport x))

variable [Invertible (2 : R)]

omit [Invertible (2 : R)] in
lemma koszulClass_succ {n : ℕ} (x : Fin (n + 1) → R) :
    koszulClass x =
    K0WithSupport.enlarge (le_of_eq (koszulClosedSupport_succ x).symm)
      (K0WithSupport.cup (oneKoszulClass (x (Fin.last n))) (koszulClass (Fin.init x))) := by
  let hp := oneKoszulComplex_perfect (x (Fin.last n))
  let hq := (isPerfectSupported_koszulComplex (Fin.init x)).strictlyPerfect
  let sp := oneKoszulComplex_support (x (Fin.last n))
  let sq := koszulComplex_closedSupport (Fin.init x)
  let h := le_of_eq (koszulClosedSupport_succ x).symm
  have he := K0WithSupport.mk_eq_of_quasiIso (koszulClosedSupport x)
    (cochainTensor (oneKoszulComplex (x (Fin.last n))) (koszulComplex (Fin.init x)))
    (koszulComplex x) (strictlyPerfectComplex_cochainTensor _ _ hp hq)
    (isPerfectSupported_koszulComplex x).strictlyPerfect
    ((sp.cochainTensor sq hp hq).mono h) (koszulComplex_closedSupport x)
    (koszulSuccTensorIso x).hom
  simp only [koszulClass, oneKoszulClass, K0WithSupport.cup_mk_mk,
    K0WithSupport.tensorClass, K0WithSupport.enlarge_mk]
  exact he.symm

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
