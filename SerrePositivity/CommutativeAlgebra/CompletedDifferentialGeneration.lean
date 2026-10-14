module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionExt
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # 完備微分の普遍微分による生成

通常微分の有限性や、通常微分から完備化への全射性を要求しない。
完備化の有限性から商の分離性を得て、元の加群の像が張ることを示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open scoped TensorProduct

/-- 有限な完備化は元の加群の像で生成される。元の加群の有限性は不要。 -/
theorem span_range_adicCompletion_of_eq_top
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R (AdicCompletion I M)] :
    Submodule.span R (Set.range (AdicCompletion.of I M)) = ⊤ := by
  let P := Submodule.span R (Set.range (AdicCompletion.of I M))
  let : IsHausdorff I (AdicCompletion I M ⧸ P) := IsHausdorff.of_le_jacobson I _ hI
  have hq : P.mkQ = 0 := by
    apply adicCompletion_linearMap_ext_of_of I I.fg_of_isNoetherianRing
    ext m
    exact (Submodule.Quotient.mk_eq_zero P).mpr (Submodule.subset_span ⟨m, rfl⟩)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero P).mp (LinearMap.congr_fun hq x)

variable {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- 普遍導分をイデアル進完備化へ送る。 -/
def completedKaehlerDerivation (I : Ideal S) :
    Derivation k S (AdicCompletion I (KaehlerDifferential k S)) :=
  (AdicCompletion.of I _).compDer (KaehlerDifferential.D k S)

@[simp] theorem completedKaehlerDerivation_apply (I : Ideal S) (s : S) :
    completedKaehlerDerivation (k := k) I s =
      AdicCompletion.of I _ (KaehlerDifferential.D k S s) := rfl

/-- 有限な完備微分は普遍微分の像で生成される。 -/
theorem span_range_completedKaehlerDerivation_eq_top [IsNoetherianRing S]
    (I : Ideal S) (hI : I ≤ Ideal.jacobson (⊥ : Ideal S))
    [Module.Finite S (AdicCompletion I (KaehlerDifferential k S))] :
    Submodule.span S (Set.range (completedKaehlerDerivation (k := k) I)) = ⊤ := by
  have h := congrArg (fun P : Submodule S (KaehlerDifferential k S) ↦
    P.map (AdicCompletion.of I _)) (KaehlerDifferential.span_range_derivation k S)
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp] at h
  exact h.trans (by simpa only [← LinearMap.coe_range, Submodule.span_eq] using
    span_range_adicCompletion_of_eq_top (M := KaehlerDifferential k S) I hI)

variable (L : Type*) [CommRing L] [Algebra S L] [Algebra k L] [IsScalarTower k S L]

/-- 完備普遍導分を同じ環上で係数拡大する。 -/
def baseChangeCompletedKaehlerDerivation (I : Ideal S) :
    Derivation k S (L ⊗[S] AdicCompletion I (KaehlerDifferential k S)) :=
  (TensorProduct.mk S L _ 1).compDer (completedKaehlerDerivation (k := k) I)

@[simp] theorem baseChangeCompletedKaehlerDerivation_apply (I : Ideal S) (s : S) :
    baseChangeCompletedKaehlerDerivation (k := k) L I s =
      1 ⊗ₜ[S] AdicCompletion.of I _ (KaehlerDifferential.D k S s) := rfl

/-- 係数拡大した有限完備微分も、同じ普遍微分の像で生成される。 -/
theorem span_range_baseChangeCompletedKaehlerDerivation_eq_top [IsNoetherianRing S]
    (I : Ideal S) (hI : I ≤ Ideal.jacobson (⊥ : Ideal S))
    [Module.Finite S (AdicCompletion I (KaehlerDifferential k S))] :
    Submodule.span L (Set.range (baseChangeCompletedKaehlerDerivation (k := k) L I)) = ⊤ := by
  have h := congrArg (fun P : Submodule S (AdicCompletion I (KaehlerDifferential k S)) ↦
    P.baseChange L) (span_range_completedKaehlerDerivation_eq_top (k := k) I hI)
  rw [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp] at h
  exact h

end SerrePositivity
