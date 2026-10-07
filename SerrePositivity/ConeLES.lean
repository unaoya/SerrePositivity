module

public import SerrePositivity.KoszulExact

/-!
# 写像錐のホモロジー長完全列（一般の射）

`φ : K ⟶ L`（`ModuleCat R` の ℤ 添字 cochain 複体）に対して、写像錐の三角
`K → L → Cone φ → K[1]` にホモロジー関手を当てた長完全列を、三つの短複体の完全性として
取り出す。`KoszulExact.lean` の `ConeSmul`（`φ = a • 𝟙 K` の場合）と同じ構成。

- `Cone.exact₂ φ n`：`H^n K → H^n L → H^n (Cone φ)`
- `Cone.exact₃ φ n₀ n₁ h`：`H^{n₀} L → H^{n₀} (Cone φ) → H^{n₁} K`
- `Cone.exact₁ φ n₀ n₁ h`：`H^{n₀} (Cone φ) → H^{n₁} K → H^{n₁} L`

Tor の長完全列（`Descent/TorLES.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

namespace Cone

variable {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- `Cone φ`。 -/
noncomputable abbrev cone : CochainComplex (ModuleCat.{u} R) ℤ := CochainComplex.mappingCone φ

lemma triangleh_distinguished :
    CochainComplex.mappingCone.triangleh φ ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished _

/-- 連結射 `δ : H^{n₀}(Cone φ) → H^{n₁}(K)`。 -/
noncomputable def δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : (cone φ).homology n₀ ⟶ K.homology n₁ :=
  (ConeSmul.e n₀ (cone φ)).inv ≫
    (ConeSmul.H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh φ) n₀ n₁ h ≫
    (ConeSmul.e n₁ K).hom

lemma δ_square (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ConeSmul.H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh φ) n₀ n₁ h ≫
        (ConeSmul.e n₁ K).hom =
      (ConeSmul.e n₀ (cone φ)).hom ≫ δ φ n₀ n₁ h := by
  rw [δ, Iso.hom_inv_id_assoc]
  rfl

/-- 三角圏側の短複体 `H^n K → H^n L → H^n (Cone φ)`。 -/
noncomputable abbrev S₂ (n : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((ConeSmul.H₀ (R := R)).homologySequence_comp _ (triangleh_distinguished φ) n)

/-- 三角圏側の短複体 `H^{n₀} L → H^{n₀} (Cone φ) → H^{n₁} K`。 -/
noncomputable abbrev S₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _
    ((ConeSmul.H₀ (R := R)).comp_homologySequenceδ _ (triangleh_distinguished φ) n₀ n₁ h)

/-- 三角圏側の短複体 `H^{n₀} (Cone φ) → H^{n₁} K → H^{n₁} L`。 -/
noncomputable abbrev S₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _
    ((ConeSmul.H₀ (R := R)).homologySequenceδ_comp _ (triangleh_distinguished φ) n₀ n₁ h)

/-- `H^n K → H^n L → H^n (Cone φ)` は完全。 -/
lemma exact₂ (n : ℤ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap φ n)
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) n)
      (comp_eq_zero_transport (S₂ φ n) (ConeSmul.e n K) (ConeSmul.e n L) (ConeSmul.e n (cone φ))
        _ _ (ConeSmul.e_naturality n φ)
        (ConeSmul.e_naturality n (CochainComplex.mappingCone.inr φ)))).Exact :=
  exact_transport ((ConeSmul.H₀ (R := R)).homologySequence_exact₂ _ (triangleh_distinguished φ) n)
    (ConeSmul.e n K) (ConeSmul.e n L) (ConeSmul.e n (cone φ)) _ _ (ConeSmul.e_naturality n φ)
    (ConeSmul.e_naturality n (CochainComplex.mappingCone.inr φ))

/-- `H^{n₀} L → H^{n₀} (Cone φ) → H^{n₁} K` は完全。 -/
lemma exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) n₀)
      (δ φ n₀ n₁ h)
      (comp_eq_zero_transport (S₃ φ n₀ n₁ h) (ConeSmul.e n₀ L) (ConeSmul.e n₀ (cone φ))
        (ConeSmul.e n₁ K) _ (δ φ n₀ n₁ h)
        (ConeSmul.e_naturality n₀ (CochainComplex.mappingCone.inr φ))
        (δ_square φ n₀ n₁ h))).Exact :=
  exact_transport
    ((ConeSmul.H₀ (R := R)).homologySequence_exact₃ _ (triangleh_distinguished φ) n₀ n₁ h)
    (ConeSmul.e n₀ L) (ConeSmul.e n₀ (cone φ)) (ConeSmul.e n₁ K) _ (δ φ n₀ n₁ h)
    (ConeSmul.e_naturality n₀ (CochainComplex.mappingCone.inr φ)) (δ_square φ n₀ n₁ h)

/-- `H^{n₀} (Cone φ) → H^{n₁} K → H^{n₁} L` は完全。 -/
lemma exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (δ φ n₀ n₁ h) (HomologicalComplex.homologyMap φ n₁)
      (comp_eq_zero_transport (S₁ φ n₀ n₁ h) (ConeSmul.e n₀ (cone φ)) (ConeSmul.e n₁ K)
        (ConeSmul.e n₁ L) (δ φ n₀ n₁ h) _ (δ_square φ n₀ n₁ h)
        (ConeSmul.e_naturality n₁ φ))).Exact :=
  exact_transport
    ((ConeSmul.H₀ (R := R)).homologySequence_exact₁ _ (triangleh_distinguished φ) n₀ n₁ h)
    (ConeSmul.e n₀ (cone φ)) (ConeSmul.e n₁ K) (ConeSmul.e n₁ L) (δ φ n₀ n₁ h) _
    (δ_square φ n₀ n₁ h) (ConeSmul.e_naturality n₁ φ)

end Cone

end SerrePositivity
