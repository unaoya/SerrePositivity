module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.HomologicalAlgebra.PerfectResidueTensorRegular
public import SerrePositivity.CommutativeAlgebra.CoefficientTensorAutomorphism
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.Algebra.CharP.Lemmas
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraH0

/-!
# 完全 δ 環のテンソル積（BS 著者版 Remark 2.7 と §2.4）

## 概要
完全 δ 環の通常テンソル積は p ねじれなしで完全 δ 構造を持ち、その古典的 p 進完備化と導来完備テンソル積 H⁰ も完全 δ 環で離散。

## 方針
両因子の Frobenius 自己同型からテンソル積の Frobenius 持ち上げを作り、p ねじれなしで δ 構造を復元する。

## 規約
一般の δ 環のテンソル積は `Delta/Basic/Tensor` で与える（A0 で Basic/DeltaColimit に作る）。

## 使われ方
完全 prism の完備テンソル積（Prism/Tensor）。旧 Prism/Tensor から移した。
-/

universe u

/-! ## The actual p-completed tensor of perfect delta rings is discrete

The p-regularity and perfect residue inputs are supplied by the original delta
structures. This proves discreteness, p-regularity and classical completeness of
H0, and does not yet construct a perfect delta structure on that H0 ring.
-/

@[expose] public noncomputable section PerfectDeltaCompletedTensorDiscrete

namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
  [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- A perfect delta algebra has regular base-scalar p action. -/
lemma perfectDeltaAlgebra_p_regular (DS : DeltaStructure p S) (hS : DS.IsPerfect) :
    IsSMulRegular (ModuleCat.of R S) (p : R) := by
  intro x y hxy
  apply hS.p_mul_injective
  change (p : R) • (show S from x) = (p : R) • (show S from y) at hxy
  simpa only [Algebra.smul_def, map_natCast] using hxy

/-- Its actual residue over the base ideal is a perfect ring. -/
lemma perfectDeltaAlgebra_perfectRing_residue (DS : DeltaStructure p S) (hS : DS.IsPerfect) :
    PerfectRing (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {(p : R)})) p := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact hS.perfectRing_mod_p

/-- The original completed tensor of perfect delta rings is discrete. -/
lemma perfectDelta_completedTensor_pure
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    let X := (boundedAboveCompletedTensorAlgebra R (p : R) S T).X
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => (p : R) • x) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact completedTensorAlgebra_pure_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)

/-- Multiplication by p on its original H0 ring is injective. -/
lemma perfectDelta_completedTensorH0_p_mul_injective
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    Function.Injective (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj =>
      (p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) * x) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact completedTensorH0_p_mul_injective_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)

/-- Its original H0 ring is classically p-adically complete. -/
lemma perfectDelta_completedTensorH0_isAdicComplete
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    let A := boundedAboveCompletedTensorAlgebra R (p : R) S T
    letI := derivedH0CommRing A
    IsAdicComplete
      (Ideal.span {(p : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)})
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact completedTensorH0_isAdicComplete_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)
end SerrePositivity.BhattScholze

end PerfectDeltaCompletedTensorDiscrete

/-! ## The ordinary tensor of perfect delta rings is p-torsion-free

This supplies the regularity input for constructing a tensor Frobenius lift.
A perfect delta structure on the tensor is not constructed here.
-/

@[expose] public noncomputable section PerfectDeltaTensorRegular

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- No flatness or completeness assumption is required on the original algebra diagram. -/
lemma perfectDelta_tensor_p_mul_injective
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect) :
    Function.Injective (fun x : S ⊗[R] T => (p : S ⊗[R] T) * x) := by
  have := hR.perfectRing_mod_p
  have := perfectDeltaAlgebra_perfectRing_residue p R S DS hS
  have := perfectDeltaAlgebra_perfectRing_residue p R T DT hT
  exact tensor_p_mul_injective_of_perfect_residue p R S T hR.p_mul_injective
    (perfectDeltaAlgebra_p_regular p R S DS hS) (perfectDeltaAlgebra_p_regular p R T DT hT)

end SerrePositivity.BhattScholze

end PerfectDeltaTensorRegular

/-! ## A perfect delta structure on the original ordinary tensor

Both algebra maps are delta maps. The factor Frobenius automorphisms give the
specified semilinear tensor automorphism, which is a Frobenius lift modulo p.
The already proved p-regularity then reconstructs the unique delta structure
with that lift. Zero tensor rings are included without CharP instances.
-/

@[expose] public noncomputable section PerfectDeltaTensorStructure

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))

/-- The factor Frobenius maps induce an automorphism with its original coefficient action. -/
def perfectDeltaTensorFrobeniusEquiv : S ⊗[R] T ≃+* S ⊗[R] T :=
  coefficientTensorAutomorphism (DR.frobeniusEquiv hR) (DS.frobeniusEquiv hS)
    (DT.frobeniusEquiv hT) (fun r => (hRS.map_frobeniusLift r).symm)
    (fun r => (hRT.map_frobeniusLift r).symm)

/-- The tensor Frobenius acts factorwise on pure tensors. -/
lemma perfectDeltaTensorFrobeniusEquiv_tmul (s : S) (t : T) :
    perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT (s ⊗ₜ[R] t) =
      DS.frobeniusLift s ⊗ₜ[R] DT.frobeniusLift t :=
  coefficientTensorAutomorphism_tmul ..

/-- Reduction modulo p is the p-th power map, including zero quotients. -/
lemma perfectDeltaTensorFrobeniusEquiv_mod_p (x : S ⊗[R] T) :
    Ideal.Quotient.mk (Ideal.span {(p : S ⊗[R] T)})
        (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT x) =
      Ideal.Quotient.mk (Ideal.span {(p : S ⊗[R] T)}) x ^ p := by
  let B := S ⊗[R] T
  let q := Ideal.Quotient.mk (Ideal.span {(p : B)})
  let iS := (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toRingHom
  let iT := (Algebra.TensorProduct.includeRight : T →ₐ[R] B).toRingHom
  have hpq : q (p : B) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hqp : (p : B ⧸ Ideal.span {(p : B)}) = 0 := by
    rw [← map_natCast q, hpq]
  have hpS : (q.comp iS) (p : S) = 0 := by rw [RingHom.comp_apply, map_natCast, hpq]
  have hpT : (q.comp iT) (p : T) = 0 := by rw [RingHom.comp_apply, map_natCast, hpq]
  have hmodS := DS.map_frobeniusLift_of_map_p_eq_zero (q.comp iS) hpS
  have hmodT := DT.map_frobeniusLift_of_map_p_eq_zero (q.comp iT) hpT
  have hprod (s : S) (t : T) : iS s * iT t = s ⊗ₜ[R] t := by
    change (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    rw [perfectDeltaTensorFrobeniusEquiv_tmul]
    change q (DS.frobeniusLift s ⊗ₜ[R] DT.frobeniusLift t) = q (s ⊗ₜ[R] t) ^ p
    rw [← hprod, ← hprod, map_mul, map_mul, mul_pow]
    exact congrArg₂ (fun x y => x * y) (hmodS s) (hmodT t)
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    have h := add_pow_prime_eq (Fact.out : p.Prime) (q x) (q y)
    simpa only [hqp, zero_mul, add_zero] using h.symm

/-- 完全 δ 環の通常のテンソル積に、両方の構造射と両立する δ 構造を載せる（BS 著者版 Remark 2.7 の押し出しの構成で完全 δ 環の場合）。 -/
def perfectDeltaTensorStructure : DeltaStructure p (S ⊗[R] T) :=
  (DeltaStructure.existsUnique_of_mod_p
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
    (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).toRingHom
    (perfectDeltaTensorFrobeniusEquiv_mod_p p R S T DR DS DT hR hS hT hRS hRT)).choose

/-- Its Frobenius lift is the specified tensor automorphism. -/
lemma perfectDeltaTensorStructure_frobeniusLift :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).frobeniusLift =
      (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).toRingHom :=
  (DeltaStructure.existsUnique_of_mod_p
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
    (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).toRingHom
    (perfectDeltaTensorFrobeniusEquiv_mod_p p R S T DR DS DT hR hS hT hRS hRT)).choose_spec.1

/-- The reconstructed tensor delta structure is perfect. -/
lemma perfectDeltaTensorStructure_isPerfect :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect := by
  rw [DeltaStructure.IsPerfect, perfectDeltaTensorStructure_frobeniusLift]
  exact (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).bijective

/-- The standard inclusion of the left factor preserves delta. -/
lemma perfectDeltaTensorStructure_includeLeft_isDeltaHom :
    DS.IsDeltaHom (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  intro s
  rw [perfectDeltaTensorStructure_frobeniusLift]
  change DS.frobeniusLift s ⊗ₜ[R] (1 : T) =
    perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT (s ⊗ₜ[R] (1 : T))
  rw [perfectDeltaTensorFrobeniusEquiv_tmul, map_one]

/-- The standard inclusion of the right factor preserves delta. -/
lemma perfectDeltaTensorStructure_includeRight_isDeltaHom :
    DT.IsDeltaHom (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  intro t
  rw [perfectDeltaTensorStructure_frobeniusLift]
  change (1 : S) ⊗ₜ[R] DT.frobeniusLift t =
    perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT ((1 : S) ⊗ₜ[R] t)
  rw [perfectDeltaTensorFrobeniusEquiv_tmul, map_one]

/-- The inverse tensor Frobenius acts by inverse factor Frobenius maps. -/
lemma perfectDeltaTensorFrobeniusEquiv_symm_tmul (s : S) (t : T) :
    (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT).symm (s ⊗ₜ[R] t) =
      (DS.frobeniusEquiv hS).symm s ⊗ₜ[R] (DT.frobeniusEquiv hT).symm t :=
  coefficientTensorAutomorphism_symm_tmul ..

/-- The original base algebra map preserves delta. -/
lemma perfectDeltaTensorStructure_algebraMap_isDeltaHom :
    DR.IsDeltaHom (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap R (S ⊗[R] T)) := by
  have h := (perfectDeltaTensorStructure_includeLeft_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT).comp hRS
  have he : (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toRingHom.comp
      (algebraMap R S) = algebraMap R (S ⊗[R] T) := by
    ext r
    exact (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes r
  rwa [he] at h

/-- The ordinary tensor lift preserves delta into any p-regular delta target. -/
lemma perfectDeltaTensorStructure_lift_isDeltaHom
    (E : Type u) [CommRing E] (DE : DeltaStructure p E)
    (hpE : Function.Injective (fun x : E => (p : E) * x))
    (fS : S →+* E) (fT : T →+* E)
    (hMatch : ∀ r, fS (algebraMap R S r) = fT (algebraMap R T r))
    (hfS : DS.IsDeltaHom DE fS) (hfT : DT.IsDeltaHom DE fT) :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom DE
      (coefficientTensorLift fS fT hMatch) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ hpE
  intro x
  rw [perfectDeltaTensorStructure_frobeniusLift]
  induction x using TensorProduct.inductionOn with
  | tmul s t =>
    change coefficientTensorLift fS fT hMatch
      (perfectDeltaTensorFrobeniusEquiv p R S T DR DS DT hR hS hT hRS hRT (s ⊗ₜ[R] t)) = _
    rw [perfectDeltaTensorFrobeniusEquiv_tmul, coefficientTensorLift_tmul,
      coefficientTensorLift_tmul, map_mul, hfS.map_frobeniusLift, hfT.map_frobeniusLift]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
end SerrePositivity.BhattScholze

end PerfectDeltaTensorStructure

/-! ## The classical p-completion of a perfect delta tensor

The original completion unit and both factor maps preserve delta. Comparison
with the original derived completed tensor H0 is a separate theorem.
-/

@[expose] public noncomputable section PerfectDeltaTensorPCompletion

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))
local notation "B" => S ⊗[R] T
local notation "Cp" => AdicCompletion (Ideal.span {(p : B)}) B

/-- The classical p-completion inherits the tensor delta structure. -/
def perfectDeltaTensorPCompletionStructure : DeltaStructure p Cp :=
  (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).adicCompletion
    (Ideal.span {(p : B)}) (Ideal.mem_span_singleton_self _)

/-- The completed delta structure is perfect. -/
lemma perfectDeltaTensorPCompletionStructure_isPerfect :
    (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect :=
  (perfectDeltaTensorStructure_isPerfect p R S T DR DS DT hR hS hT hRS hRT).adicCompletion_span_p

/-- The original completion unit preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_unit_isDeltaHom :
    (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom
      (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap B Cp) :=
  (perfectDeltaTensorStructure p R S T DR DS DT hR hS hT hRS hRT).isDeltaHom_adicCompletion
    (Ideal.span {(p : B)}) (Ideal.mem_span_singleton_self _)

/-- The original completed left factor map preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_includeLeft_isDeltaHom :
    DS.IsDeltaHom (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      ((algebraMap B Cp).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] B).toRingHom) :=
  (perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT).comp
    (perfectDeltaTensorStructure_includeLeft_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)

/-- The original completed right factor map preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_includeRight_isDeltaHom :
    DT.IsDeltaHom (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      ((algebraMap B Cp).comp
        (Algebra.TensorProduct.includeRight : T →ₐ[R] B).toRingHom) :=
  (perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT).comp
    (perfectDeltaTensorStructure_includeRight_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)

/-- The original completed coefficient map preserves delta. -/
lemma perfectDeltaTensorPCompletionStructure_base_isDeltaHom :
    DR.IsDeltaHom (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      ((algebraMap B Cp).comp (algebraMap R B)) :=
  (perfectDeltaTensorPCompletionStructure_unit_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT).comp
    (perfectDeltaTensorStructure_algebraMap_isDeltaHom p R S T DR DS DT hR hS hT hRS hRT)
end SerrePositivity.BhattScholze

end PerfectDeltaTensorPCompletion

/-! ## A perfect delta structure on the original completed derived tensor H0

The original H0 ring is compared with the classical completion preserving the
unit, coefficient map, and factor maps. The perfect delta structure is transported
through that exact ring equivalence. The subsequent d-completion is separate.
-/

@[expose] public noncomputable section PerfectDeltaCompletedTensorH0

namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- Transport of a perfect delta structure through a ring equivalence stays perfect. -/
lemma DeltaStructure.IsPerfect.comapEquiv {p : ℕ} [Fact p.Prime]
    {X Y : Type u} [CommRing X] [CommRing Y] {E : DeltaStructure p Y}
    (hE : E.IsPerfect) (e : X ≃+* Y) : (E.comapEquiv e).IsPerfect := by
  have he := E.comapEquiv_isDeltaHom e
  have hf (x : X) : e ((E.comapEquiv e).frobeniusLift x) = E.frobeniusLift (e x) :=
    he.map_frobeniusLift x
  constructor
  · intro x y hxy
    apply e.injective
    apply hE.injective
    rw [← hf, ← hf, hxy]
  · intro x
    obtain ⟨y, hy⟩ := hE.surjective (e x)
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [hf, e.apply_symm_apply, hy]

variable (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (DR : DeltaStructure p R) (DS : DeltaStructure p S) (DT : DeltaStructure p T)
    (hR : DR.IsPerfect) (hS : DS.IsPerfect) (hT : DT.IsPerfect)
    (hRS : DR.IsDeltaHom DS (algebraMap R S))
    (hRT : DR.IsDeltaHom DT (algebraMap R T))
local notation "B" => S ⊗[R] T
local notation "Cp" => AdicCompletion (Ideal.span {(p : B)}) B
-- This carrier notation contains functor projections; only its syntax precheck is disabled.
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj

/-- The original completed tensor H0 receives the transported delta structure. -/
def perfectDeltaCompletedTensorH0Structure :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DeltaStructure p H := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).comapEquiv
    (completedTensorH0AdicRingEquiv R p S T
      (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT))

/-- The delta structure on the actual H0 ring is perfect. -/
lemma perfectDeltaCompletedTensorH0Structure_isPerfect :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaTensorPCompletionStructure_isPerfect p R S T DR DS DT hR hS hT hRS hRT).comapEquiv
    (completedTensorH0AdicRingEquiv R p S T
      (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT))

/-- The standard comparison with classical completion preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsDeltaHom
      (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0AdicRingEquiv R p S T
        (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)).toRingHom := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT).comapEquiv_isDeltaHom
    (completedTensorH0AdicRingEquiv R p S T
      (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT))

/-- The original left factor map on actual H0, normalized by the standard single comparison. -/
def completedTensorH0LeftRingHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    S →+* H := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃+* S :=
    derivedSingleH0RingEquiv (R := R) S
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T)).toRingHom.comp
    eS.symm.toRingHom

/-- The original right factor map on actual H0, normalized by the standard single comparison. -/
def completedTensorH0RightRingHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    T →+* H := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃+* T :=
    derivedSingleH0RingEquiv (R := R) T
  exact (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T)).toRingHom.comp
    eT.symm.toRingHom


omit [Fact p.Prime] in
/-- The original left factor map agrees with the classical completed inclusion. -/
lemma completedTensorH0LeftRingHom_comparison
    (hB : IsSMulRegular B (p : B)) (x : S) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB (completedTensorH0LeftRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) S)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) S)
  let eS : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj ≃+* S :=
    derivedSingleH0RingEquiv (R := R) S
  change completedTensorH0AdicRingEquiv R p S T hB
    (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R (p : R) S T)
      (eS.symm x)) = _
  rw [completedTensorH0AdicRingEquiv_left]
  have hx : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
      (ModuleCat.of R S) (eS.symm x) = x :=
    eS.apply_symm_apply x
  rw [hx]

omit [Fact p.Prime] in
/-- The original right factor map agrees with the classical completed inclusion. -/
lemma completedTensorH0RightRingHom_comparison
    (hB : IsSMulRegular B (p : B)) (x : T) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    completedTensorH0AdicRingEquiv R p S T hB (completedTensorH0RightRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) T)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) T)
  let eT : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj ≃+* T :=
    derivedSingleH0RingEquiv (R := R) T
  change completedTensorH0AdicRingEquiv R p S T hB
    (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R (p : R) S T)
      (eT.symm x)) = _
  rw [completedTensorH0AdicRingEquiv_right]
  have hx : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
      (ModuleCat.of R T) (eT.symm x) = x :=
    eT.apply_symm_apply x
  rw [hx]

/-- The original left factor map preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_includeLeft_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DS.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0LeftRingHom p R S T) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let e := completedTensorH0AdicRingEquiv R p S T
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  let DH := perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
  let DC := perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT
  have he := perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hf := perfectDeltaTensorPCompletionStructure_includeLeft_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hx (x : S) : e (completedTensorH0LeftRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) x) :=
    completedTensorH0LeftRingHom_comparison p R S T _ x
  change DS.IsDeltaHom DH (completedTensorH0LeftRingHom p R S T)
  intro x
  apply e.injective
  calc
    _ = algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) (DS.delta x)) := hx _
    _ = DC.delta (algebraMap B Cp ((Algebra.TensorProduct.includeLeft : S →ₐ[R] B) x)) := hf x
    _ = DC.delta (e (completedTensorH0LeftRingHom p R S T x)) := congrArg DC.delta (hx x).symm
    _ = _ := (he _).symm

/-- The original right factor map preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_includeRight_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DT.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (completedTensorH0RightRingHom p R S T) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let e := completedTensorH0AdicRingEquiv R p S T
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  let DH := perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
  let DC := perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT
  have he := perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hf := perfectDeltaTensorPCompletionStructure_includeRight_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hx (x : T) : e (completedTensorH0RightRingHom p R S T x) =
      algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) x) :=
    completedTensorH0RightRingHom_comparison p R S T _ x
  change DT.IsDeltaHom DH (completedTensorH0RightRingHom p R S T)
  intro x
  apply e.injective
  calc
    _ = algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) (DT.delta x)) := hx _
    _ = DC.delta (algebraMap B Cp ((Algebra.TensorProduct.includeRight : T →ₐ[R] B) x)) := hf x
    _ = DC.delta (e (completedTensorH0RightRingHom p R S T x)) := congrArg DC.delta (hx x).symm
    _ = _ := (he _).symm

/-- The original H0 coefficient algebra map preserves delta. -/
lemma perfectDeltaCompletedTensorH0Structure_base_isDeltaHom :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    DR.IsDeltaHom (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT)
      (algebraMap R H) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let e := completedTensorH0AdicRingEquiv R p S T
    (perfectDelta_tensor_p_mul_injective p R S T DR DS DT hR hS hT)
  let DH := perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT
  let DC := perfectDeltaTensorPCompletionStructure p R S T DR DS DT hR hS hT hRS hRT
  have he := perfectDeltaCompletedTensorH0Structure_comparison_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hf := perfectDeltaTensorPCompletionStructure_base_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT
  have hx (r : R) : e (algebraMap R H r) = algebraMap B Cp (algebraMap R B r) :=
    completedTensorH0AdicRingEquiv_algebraMap R p S T _ r
  change DR.IsDeltaHom DH (algebraMap R H)
  intro r
  apply e.injective
  calc
    _ = algebraMap B Cp (algebraMap R B (DR.delta r)) := hx _
    _ = DC.delta (algebraMap B Cp (algebraMap R B r)) := hf r
    _ = DC.delta (e (algebraMap R H r)) := congrArg DC.delta (hx r).symm
    _ = _ := (he _).symm

/-- The original p-completed tensor is discrete and its actual H0 delta structure is perfect. -/
lemma perfectDeltaCompletedTensor_discrete_perfect :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 ∧
        (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsPerfect := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  have hpure := perfectDelta_completedTensor_pure p R S T DR DS DT hR hS hT
  exact ⟨hpure.1, hpure.2.1,
    perfectDeltaCompletedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT⟩

/-- A distinguished base element remains distinguished on actual H0. -/
lemma perfectDeltaCompletedTensorH0Structure_distinguished (d : R) (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    (perfectDeltaCompletedTensorH0Structure p R S T DR DS DT hR hS hT hRS hRT).IsDistinguished
      (algebraMap R H d) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  exact (perfectDeltaCompletedTensorH0Structure_base_isDeltaHom p R S T DR DS DT
    hR hS hT hRS hRT).map_isDistinguished hd

include hR hS hT hRS hRT in
/-- Its image is regular on actual H0, using the proved p-adic completeness. -/
lemma perfectDeltaCompletedTensorH0Structure_distinguished_regular
    (d : R) (hd : DR.IsDistinguished d) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    Function.Injective (fun x : H => algebraMap R H d * x) := by
  let := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  let := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  have : IsAdicComplete (Ideal.span {(p : H)}) H :=
    perfectDelta_completedTensorH0_isAdicComplete p R S T DR DS DT hR hS hT
  have hperf := perfectDeltaCompletedTensorH0Structure_isPerfect p R S T DR DS DT hR hS hT hRS hRT
  exact hperf.distinguished_mul_injective
      (perfectDeltaCompletedTensorH0Structure_distinguished p R S T DR DS DT hR hS hT hRS hRT d hd)
end SerrePositivity.BhattScholze

end PerfectDeltaCompletedTensorH0

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.7" (partial := special) "通常のテンソル積（p 正則性なし、BS-W15）、有向余極限、完全 δ 環のテンソル、w_R : R → W(R)（ghost 単射かつ p ねじれなしのとき）。一般の極限・余極限、W が右随伴であることは未 ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.perfectDeltaTensorStructure
