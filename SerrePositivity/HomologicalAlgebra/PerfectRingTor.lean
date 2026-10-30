module

public import SerrePositivity.CommutativeAlgebra.PerfectPolynomial
public import SerrePositivity.HomologicalAlgebra.PerfectRadicalQuotientTor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationIso
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
/-! # Tor independence for arbitrary diagrams of perfect characteristic-p rings

A free perfect polynomial presentation is flat over the original perfect base.
Acyclic base change reduces arbitrary maps to the already proved surjective case.
The `(p : R) = 0` wrappers admit zero base rings and zero target rings without CharP instances.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] [PerfectRing R p]

/-- All positive Tor vanishes for any two perfect algebras over a perfect base. -/
lemma perfectRing_tor_subsingleton (S : Type u) [CommRing S] [Algebra R S] [PerfectRing S p]
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p] (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i S C) := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · have := hS
    exact torModule_subsingleton_left S C i
  rcases subsingleton_or_nontrivial C with hC | hC
  · have := hC
    exact torModule_subsingleton_right_of_subsingleton S C i
  have := hS
  have := hC
  have hpS : (p : S) = 0 := by
    rw [← map_natCast (algebraMap R S), CharP.cast_eq_zero, map_zero]
  have hpC : (p : C) = 0 := by
    rw [← map_natCast (algebraMap R C), CharP.cast_eq_zero, map_zero]
  have : CharP S p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpS
  have : CharP C p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpC
  let P := PerfectPolynomial p R S
  let e : P →ₐ[R] S := perfectPolynomialEval p R S S id
  let : Algebra P S := e.toRingHom.toAlgebra
  let : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  have : Module.Flat R P := perfectPolynomial_flat p R S
  let E := P ⊗[R] C
  have : PerfectRing E p := perfectCoefficientTensor_perfectRing p R P C
  have he : Function.Surjective (algebraMap P S) := perfectPolynomialEval_surjective p R S
  have ht := perfectRing_surjective_tor_subsingleton (p := p) S he E i hi
  let L := (ModuleCat.extendScalars (algebraMap R P)).obj (ModuleCat.of R C)
  let eqL := moduleCatBaseChangeTensorEquiv (R := R) (B := P) (ModuleCat.of R C)
  have hT : Subsingleton (TorModule P i S L) :=
    torModule_subsingleton_of_linearEquiv S eqL.symm i ht
  have hz : IsZero (((Tor (ModuleCat P) i).obj (ModuleCat.of P S)).obj L) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact hT
  let bc := torAcyclicBaseChangeIso (algebraMap R P) (ModuleCat.of R C)
    (scalarExtensionTorVanishing_of_flat_algebra (R := R) (B := P) (ModuleCat.of R C))
    (ModuleCat.of P S) i
  have hres := ((ModuleCat.restrictScalars (algebraMap R P)).map_isZero hz).of_iso bc
  let eqS : (ModuleCat.restrictScalars (algebraMap R P)).obj (ModuleCat.of P S) ≃ₗ[R] S :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => by
        change algebraMap R P r • (show S from s) = r • (show S from s)
        rw [← IsScalarTower.algebraMap_smul P r (show S from s)] }
  let et := ((Tor (ModuleCat R) i).mapIso eqS.toModuleIso).app (ModuleCat.of R C)
  exact ModuleCat.subsingleton_of_isZero (hres.of_iso et.symm)

/-- The same Tor vanishing allows a zero base ring via an explicit p=0 hypothesis. -/
lemma perfectRing_tor_subsingleton_of_char_eq_zero
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [PerfectRing R p]
    (hp : (p : R) = 0) (S : Type u) [CommRing S] [Algebra R S] [PerfectRing S p]
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p] (i : ℕ) (hi : 0 < i) :
    Subsingleton (TorModule R i S C) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    have := Module.subsingleton R S
    exact torModule_subsingleton_left S C i
  · have := hR
    have : CharP R p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
    exact perfectRing_tor_subsingleton S C i hi

/-- The original algebra augmentation is invertible, including zero base rings. -/
lemma perfectRing_derivedTensorAlgebraAugmentation_isIso_of_char_eq_zero
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [PerfectRing R p]
    (hp : (p : R) = 0) (S : Type u) [CommRing S] [Algebra R S] [PerfectRing S p]
    (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p] :
    IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S C).hom.hom := by
  apply derivedTensorAlgebraAugmentation_isIso_of_tor
  intro i hi
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact perfectRing_tor_subsingleton_of_char_eq_zero p R hp S C i hi
end SerrePositivity
