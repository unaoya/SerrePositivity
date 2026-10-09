module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# スカラー倍 `a • 𝟙 K` の写像錐と長完全列

- `smulId a K = a • 𝟙 K`。
- ホモトピー圏のホモロジー関手から複体のホモロジーへ、完全性と合成零を移す補題
  （`exact_transport`、`comp_eq_zero_transport`）。
- `ConeSmul`：`Cone(a • 𝟙 K)` の三角形と、そのホモロジー長完全列 `exact₁`、`exact₂`、`exact₃`。

Koszul 複体の完全性（`CommutativeAlgebra/KoszulExact.lean`）と、一般の射の写像錐の長完全列
（`HomologicalAlgebra/ConeLES.lean`）がこれを使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 複体 `K` の自己射 `a • 𝟙 K`。 -/
noncomputable def smulId (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) : K ⟶ K :=
  a • 𝟙 K

/-- 複体の射のスカラー倍はホモロジーの射のスカラー倍を誘導する。 -/
lemma homologyMap_smul {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (a : R) (i : ℤ) :
    HomologicalComplex.homologyMap (a • f) i = a • HomologicalComplex.homologyMap f i := by
  have : (HomologicalComplex.shortComplexFunctor _ _ i).map (a • f) =
      a • (HomologicalComplex.shortComplexFunctor _ _ i).map f := by
    ext <;> rfl
  simp only [HomologicalComplex.homologyMap, this, ShortComplex.homologyMap_smul]
  rfl

/-- 短複体 `S` と同型な対象で置き換えた射の合成も零。 -/
lemma comp_eq_zero_transport (S : ShortComplex (ModuleCat.{u} R))
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ g) : f ≫ g = 0 := by
  have hf : f = e₁.inv ≫ S.f ≫ e₂.hom := by rw [h₁, Iso.inv_hom_id_assoc]
  have hg : g = e₂.inv ≫ S.g ≫ e₃.hom := by rw [h₂, Iso.inv_hom_id_assoc]
  rw [hf, hg, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc,
    zero_comp, comp_zero]

/-- 短複体の完全性を、同型な対象で置き換えた短複体に移す。 -/
lemma exact_transport {S : ShortComplex (ModuleCat.{u} R)} (hS : S.Exact)
    {X₁ X₂ X₃ : ModuleCat.{u} R} (e₁ : S.X₁ ≅ X₁) (e₂ : S.X₂ ≅ X₂) (e₃ : S.X₃ ≅ X₃)
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (h₁ : S.f ≫ e₂.hom = e₁.hom ≫ f)
    (h₂ : S.g ≫ e₃.hom = e₂.hom ≫ g) :
    (ShortComplex.mk f g (comp_eq_zero_transport S e₁ e₂ e₃ f g h₁ h₂)).Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm) hS

namespace ConeSmul

variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : R)

/-- `Cone(a • 𝟙 K)`。 -/
noncomputable abbrev cone : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (smulId a K)

/-- 三角 `K → K → Cone → K[1]` は distinguished。 -/
lemma triangleh_distinguished :
    CochainComplex.mappingCone.triangleh (smulId a K) ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished _

/-- ホモロジー関手 `H^0`（shift で `H^n` が出る）。 -/
noncomputable abbrev H₀ :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤ ModuleCat.{u} R :=
  HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0

/-- ホモトピー圏のホモロジー関手と複体のホモロジーの同一視。 -/
noncomputable abbrev e (n : ℤ) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj L) ≅ L.homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app L

lemma e_naturality (n : ℤ) {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ L') :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map f) ≫ (e n L').hom =
      (e n L).hom ≫ HomologicalComplex.homologyMap f n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).hom.naturality f

/-- 連結射 `δ : H^n(Cone) → H^{n+1}(K)`。 -/
noncomputable def δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (cone K a).homology n₀ ⟶ K.homology n₁ :=
  (e n₀ (cone K a)).inv ≫
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh (smulId a K)) n₀ n₁ h ≫
    (e n₁ K).hom

lemma δ_square (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh (smulId a K)) n₀ n₁ h ≫
        (e n₁ K).hom =
      (e n₀ (cone K a)).hom ≫ δ K a n₀ n₁ h := by
  rw [δ, Iso.hom_inv_id_assoc]
  rfl

/-- 三角圏側の短複体 `H^n(K) → H^n(K) → H^n(Cone)`。 -/
noncomputable abbrev S₂ (n : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).homologySequence_comp _ (triangleh_distinguished K a) n)

/-- 三角圏側の短複体 `H^n(K) → H^n(Cone) → H^{n+1}(K)`。 -/
noncomputable abbrev S₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).comp_homologySequenceδ _ (triangleh_distinguished K a) n₀ n₁ h)

/-- 三角圏側の短複体 `H^n(Cone) → H^{n+1}(K) → H^{n+1}(K)`。 -/
noncomputable abbrev S₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).homologySequenceδ_comp _ (triangleh_distinguished K a) n₀ n₁ h)

/-- `H^n(K) → H^n(K) → H^n(Cone)` は完全。 -/
lemma exact₂ (n : ℤ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (smulId a K) n)
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (smulId a K)) n)
      (comp_eq_zero_transport (S₂ K a n) (e n K) (e n K) (e n (cone K a)) _ _
        (e_naturality n (smulId a K))
        (e_naturality n (CochainComplex.mappingCone.inr (smulId a K))))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₂ _ (triangleh_distinguished K a) n)
    (e n K) (e n K) (e n (cone K a)) _ _ (e_naturality n (smulId a K))
    (e_naturality n (CochainComplex.mappingCone.inr (smulId a K)))

/-- `H^n(K) → H^n(Cone) → H^{n+1}(K)` は完全。 -/
lemma exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (smulId a K)) n₀)
      (δ K a n₀ n₁ h)
      (comp_eq_zero_transport (S₃ K a n₀ n₁ h) (e n₀ K) (e n₀ (cone K a)) (e n₁ K) _
        (δ K a n₀ n₁ h) (e_naturality n₀ (CochainComplex.mappingCone.inr (smulId a K)))
        (δ_square K a n₀ n₁ h))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₃ _ (triangleh_distinguished K a) n₀ n₁ h)
    (e n₀ K) (e n₀ (cone K a)) (e n₁ K) _ (δ K a n₀ n₁ h)
    (e_naturality n₀ (CochainComplex.mappingCone.inr (smulId a K))) (δ_square K a n₀ n₁ h)

/-- `H^n(Cone) → H^{n+1}(K) → H^{n+1}(K)` は完全。 -/
lemma exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (δ K a n₀ n₁ h) (HomologicalComplex.homologyMap (smulId a K) n₁)
      (comp_eq_zero_transport (S₁ K a n₀ n₁ h) (e n₀ (cone K a)) (e n₁ K) (e n₁ K)
        (δ K a n₀ n₁ h) _ (δ_square K a n₀ n₁ h) (e_naturality n₁ (smulId a K)))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₁ _ (triangleh_distinguished K a) n₀ n₁ h)
    (e n₀ (cone K a)) (e n₁ K) (e n₁ K) (δ K a n₀ n₁ h) _ (δ_square K a n₀ n₁ h)
    (e_naturality n₁ (smulId a K))

end ConeSmul

end SerrePositivity
