module
public import SerrePositivity.PerfectComplex.KoszulTensor
public import SerrePositivity.PerfectComplex.ClosedSupport.Cup

/-! # Supported Koszul and unit classes independent of an Adams operation -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

def oneKoszulClass (a : R) : K0WithSupport (oneKoszulSupport a) :=
  K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
    (oneKoszulComplex a) (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))

/-- A single shift negates the Koszul class, independently of an Adams operation. -/
lemma oneKoszulClass_shift_one (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      ((oneKoszulComplex a)⟦(1 : ℤ)⟧)
      (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
      ((oneKoszulComplex_support a).shift 1)) = -oneKoszulClass a :=
  ClosedSupportShortExactAdditive.shift_one
    (K0WithSupport.mk_shortExact (oneKoszulSupport a))
    (fun e => K0WithSupport.mk_iso (oneKoszulSupport a) e)
    (oneKoszulComplex a) (oneKoszulComplex_perfect a) (oneKoszulComplex_support a)

lemma oneKoszulUnit_perfect : strictlyPerfectComplex R (oneKoszulUnit (R := R)) :=
  (isPerfectSupported_koszulComplex (fun i : Fin 0 => Fin.elim0 i)).strictlyPerfect

lemma oneKoszulUnit_support :
    HasHomologySupportOn (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R))
      (oneKoszulUnit (R := R)) :=
  fun _ => Set.subset_univ _

def cyclicUnitClass : K0WithSupport (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) :=
  K0WithSupport.mk ⊤ (supportedPerfectOnObj ⊤ (oneKoszulUnit (R := R))
    oneKoszulUnit_perfect oneKoszulUnit_support)

lemma koszulClosedSupport_zero (x : Fin 0 → R) :
    koszulClosedSupport x = (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) := by
  apply SetLike.coe_injective
  ext p
  simp [koszulClosedSupport]

def koszulClass {n : ℕ} (x : Fin n → R) : K0WithSupport (koszulClosedSupport x) :=
  K0WithSupport.mk (koszulClosedSupport x) (supportedPerfectOnObj (koszulClosedSupport x)
    (koszulComplex x) (isPerfectSupported_koszulComplex x).strictlyPerfect
    (koszulComplex_closedSupport x))

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

end Adams
end SerrePositivity
