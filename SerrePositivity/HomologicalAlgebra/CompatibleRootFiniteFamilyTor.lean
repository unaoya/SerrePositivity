module

public import SerrePositivity.HomologicalAlgebra.CompatibleRootQuotientTor
public import SerrePositivity.HomologicalAlgebra.QuotientSupTorComparison
public import SerrePositivity.HomologicalAlgebra.ModuleBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.LocalFlatnessCriterion
public import SerrePositivity.CommutativeAlgebra.CompatibleRoot
public import SerrePositivity.CommutativeAlgebra.PerfectRing
public import Mathlib.Data.Finset.Lattice.Fold
/-! # Higher Tor vanishes for finite families of compatible roots over a perfect ring

The coefficient algebra is perfect; no flatness or regularity of the roots is assumed.
Both zero intermediate quotients and zero coefficient tensors are included.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Finite root-family quotients are Tor-independent from every perfect coefficient algebra. -/
lemma compatibleRootFiniteFamilyQuotient_tor_subsingleton {p : ℕ} [Fact p.Prime] {σ : Type u} (s : Finset σ) :
    ∀ (R : Type u) [CommRing R] [CharP R p] [PerfectRing R p]
      (κ : σ → ℕ → R) (hκ : ∀ a n, κ a (n + 1) ^ p = κ a n)
      (C : Type u) [CommRing C] [Algebra R C] [PerfectRing C p]
      (i : ℕ), 0 < i →
      Subsingleton (TorModule R i (R ⧸ (s.sup fun a => compatibleRootIdeal (κ a))) C) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro R _ _ _ κ hκ C _ _ _ i hi
    rw [Finset.sup_empty]
    let e : (R ⧸ (⊥ : Ideal R)) ≃ₗ[R] R := (AlgEquiv.quotientBot R R).toLinearEquiv
    letI : Module.Flat R (R ⧸ (⊥ : Ideal R)) := Module.Flat.of_linearEquiv e
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact torModule_subsingleton_of_flat (R := R) (R ⧸ (⊥ : Ideal R)) C j
  | @insert a s ha ih =>
    intro R _ _ _ κ hκ C _ _ _ i hi
    let I := compatibleRootIdeal (κ a)
    let J : Ideal R := s.sup fun b => compatibleRootIdeal (κ b)
    have hideal : ((insert a s).sup fun b => compatibleRootIdeal (κ b)) = I ⊔ J := by
      rw [Finset.sup_insert]
    rw [hideal]
    letI : IsReduced R := isReduced_of_perfectPower R p (Fact.out : p.Prime).one_lt
    letI : IsReduced C := isReduced_of_perfectPower C p (Fact.out : p.Prime).one_lt
    have hM : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R C) := by
      intro j hj
      have := compatibleRootQuotient_tor_subsingleton (κ a) (hκ a) C j hj
      let es := baseChangeScalarAlgebraEquiv (R := R) (B := R ⧸ I)
      exact (ModuleCat.isZero_of_subsingleton
        (((Tor (ModuleCat R) j).obj (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of R C))).of_iso
          (((Tor (ModuleCat R) j).mapIso es.toModuleIso).app (ModuleCat.of R C))
    let B := R ⧸ I
    let φ : R →+* B := Ideal.Quotient.mk I
    let L := (ModuleCat.extendScalars φ).obj (ModuleCat.of R C)
    let NB := ModuleCat.of B (B ⧸ J.map φ)
    let e := quotientSupTorAcyclicBaseChangeIso I J (ModuleCat.of R C) hM i
    have hTorB : Subsingleton (TorModule B i NB L) := by
      rcases subsingleton_or_nontrivial B with hB | hB
      · letI := hB
        letI := Module.subsingleton B L
        exact torModule_subsingleton_right_of_subsingleton NB L i
      · letI := hB
        have hpB : (p : B) = 0 := by
          rw [← map_natCast φ, CharP.cast_eq_zero, map_zero]
        letI : CharP B p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpB
        letI : PerfectRing B p := compatibleRootQuotient_perfectRing (κ a) (hκ a)
        rcases subsingleton_or_nontrivial C with hC | hC
        · letI := hC
          letI : Subsingleton (B ⊗[R] C) := inferInstance
          let eqL := moduleCatBaseChangeTensorEquiv (R := R) (B := B) (ModuleCat.of R C)
          letI : Subsingleton L := eqL.injective.subsingleton
          exact torModule_subsingleton_right_of_subsingleton NB L i
        · letI := hC
          have hpC : (p : C) = 0 := by
            rw [← map_natCast (algebraMap R C), CharP.cast_eq_zero, map_zero]
          letI : CharP C p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpC
          let E := B ⊗[R] C
          letI : PerfectRing E p := perfectCoefficientTensor_perfectRing p R B C
          let κ' (b : σ) (n : ℕ) : B := φ (κ b n)
          have hκ' : ∀ b n, κ' b (n + 1) ^ p = κ' b n := by
            intro b n
            exact (map_pow φ _ _).symm.trans (congrArg φ (hκ b n))
          have hJ : J.map φ = s.sup (fun b => compatibleRootIdeal (κ' b)) := by
            dsimp only [J]
            simp only [Finset.sup_eq_iSup, Ideal.map_iSup, compatibleRootIdeal_map]
            rfl
          have hT := ih B κ' hκ' E i hi
          rw [← hJ] at hT
          let eqL := moduleCatBaseChangeTensorEquiv (R := R) (B := B) (ModuleCat.of R C)
          exact torModule_subsingleton_of_linearEquiv NB eqL.symm i hT
    letI := hTorB
    have hz : IsZero (((Tor (ModuleCat B) i).obj NB).obj L) := ModuleCat.isZero_of_subsingleton _
    exact ModuleCat.subsingleton_of_isZero
      (((ModuleCat.restrictScalars φ).map_isZero hz).of_iso e)
end SerrePositivity
