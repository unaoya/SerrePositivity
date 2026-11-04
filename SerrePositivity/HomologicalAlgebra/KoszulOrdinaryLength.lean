module

public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.LengthAlgebra.Core

/-! # 環同型による Koszul 複体の通常長さの不変性 -/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 環同型は Koszul ホモロジーの各次数の通常長さを保つ。 -/
lemma length_homology_koszul_equiv (σ : R ≃+* S) {e : ℕ} (x : Fin e → R) (q : ℤ) :
    Module.length S ((koszulComplex (σ ∘ x)).homology q) =
      Module.length R ((koszulComplex x).homology q) := by
  exact (((HomologicalComplex.homologyFunctor _ _ q).mapIso
    (baseChangeKoszulIso σ.toRingHom x)).toLinearEquiv.length_eq).symm.trans
      (length_homology_baseChange_equiv σ (koszulComplex x) q)

/-- 係数写像を自己同型でひねっても、通常長さに関する Koszul 有限性は保たれる。 -/
lemma ordinary_koszul_finite_comp_equiv (φ : R →+* S) (σ : S ≃+* S)
    {e : ℕ} (z : Fin e → R)
    (hfin : ∀ v : ℕ, 0 < v → ∀ q,
      (NormalizedLength.ordinary S).len ((koszulComplex (fun j ↦ φ (z j) ^ v)).homology q) ≠ ⊤) :
    ∀ v : ℕ, 0 < v → ∀ q,
      (NormalizedLength.ordinary S).len
        ((koszulComplex (fun j ↦ (σ.toRingHom.comp φ) (z j) ^ v)).homology q) ≠ ⊤ := by
  intro v hv q
  have hx : (fun j ↦ (σ.toRingHom.comp φ) (z j) ^ v) = σ ∘ (fun j ↦ φ (z j) ^ v) := by
    funext j
    exact (map_pow σ _ _).symm
  rw [hx]
  change (Module.length S ((koszulComplex (σ ∘ (fun j ↦ φ (z j) ^ v))).homology q) : ℝ≥0∞) ≠ ⊤
  rw [length_homology_koszul_equiv]
  exact hfin v hv q

end SerrePositivity
