module

public import SerrePositivity.KoszulBaseChange
public import SerrePositivity.KoszulResolution
public import SerrePositivity.TorCochain

/-!
# `Tor` と Koszul ホモロジー

`z` の Koszul 複体が `A/(z)` の分解なら、`A` 代数 `C`（構造は `φ : A →+* C`）に対して

  `Tor_i^A(A/(z), C) ≅ H_i(φ z; C)`

（左辺は `TorAlg φ i (A ⧸ (z))`）。`torIsoCochain` と、基底変更が Koszul 複体と両立すること
（`baseChangeKoszulIso`）による。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- **`Tor` と Koszul ホモロジー**：`Tor_i^A(A/(z), C) ≅ H_i(φ z; C)`。 -/
noncomputable def torAlgKoszulIso {n : ℕ} (z : Fin n → A) (hz : IsKoszulResolution z) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range z))) ≅
      (koszulComplex (φ ∘ z)).homology (-(i : ℤ)) :=
  torIsoCochain φ (isResolutionOf_koszul z hz) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso (baseChangeKoszulIso φ z)

/-- `torAlgKoszulIso` の線形同値版。 -/
noncomputable def torAlgKoszulEquiv {n : ℕ} (z : Fin n → A) (hz : IsKoszulResolution z) (i : ℕ) :
    TorAlg φ i (A ⧸ Ideal.span (Set.range z)) ≃ₗ[C] koszulHomologySelf (φ ∘ z) i :=
  (torAlgKoszulIso φ z hz i).toLinearEquiv

end SerrePositivity
