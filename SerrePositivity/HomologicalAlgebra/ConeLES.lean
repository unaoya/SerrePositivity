module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# 写像錐のホモロジー長完全列

`φ : K ⟶ L`（`ModuleCat R` の ℤ 添字 cochain 複体）に対して、写像錐の三角
`K → L → Cone φ → K[1]` にホモトピー圏のホモロジー関手（homological functor）を当てた長完全列を、
三つの短複体の完全性として取り出す。

- `Cone.exact₂ φ n`：`H^n K → H^n L → H^n (Cone φ)`
- `Cone.exact₃ φ n₀ n₁ h`：`H^{n₀} L → H^{n₀} (Cone φ) → H^{n₁} K`
- `Cone.exact₁ φ n₀ n₁ h`：`H^{n₀} (Cone φ) → H^{n₁} K → H^{n₁} L`

ホモトピー圏のホモロジー関手と複体のホモロジーの同一視 `Cone.e` と、短複体の完全性を同型で移す
補題 `exact_transport` を経由する。`φ = smulId a K`（Koszul 複体の完全性、
`CommutativeAlgebra/KoszulResolution.lean`）、Tor の長完全列（`TorLES.lean`）、Euler 評価の加法性
（`PerfectComplex/NormalizedEuler.lean`）に使う。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 短複体の移送 -/

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

namespace Cone

/-! ## ホモトピー圏のホモロジー関手 -/

/-- ホモロジー関手 `H^0`（shift で `H^n` が出る）。 -/
noncomputable abbrev H₀ :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤ ModuleCat.{u} R :=
  HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0

/-- ホモトピー圏のホモロジー関手と複体のホモロジーの同一視。 -/
noncomputable abbrev e (n : ℤ) (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj L) ≅ L.homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app L

/-- ホモトピー圏のホモロジーと複体のホモロジーを結ぶ同型は、複体の射と両立する。 -/
lemma e_naturality (n : ℤ) {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ L') :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map f) ≫ (e n L').hom =
      (e n L).hom ≫ HomologicalComplex.homologyMap f n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).hom.naturality f

/-! ## 写像錐の長完全列 -/

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L)

/-- 複体の射 `φ : K → L` の写像錐。長完全列に現れる第三の複体を表す。 -/
noncomputable abbrev cone : CochainComplex (ModuleCat.{u} R) ℤ := CochainComplex.mappingCone φ

/-- 写像錐から作る三角形は、ホモトピー圏の完全三角形である。 -/
lemma triangleh_distinguished :
    CochainComplex.mappingCone.triangleh φ ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished _

/-- 連結射 `δ : H^{n₀}(Cone φ) → H^{n₁}(K)`。 -/
noncomputable def δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : (cone φ).homology n₀ ⟶ K.homology n₁ :=
  (e n₀ (cone φ)).inv ≫
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh φ) n₀ n₁ h ≫
    (e n₁ K).hom

/-- 写像錐の連結写像とホモトピー圏の三角形から得た写像が、ホモロジーの同一視のもとで一致する。 -/
lemma δ_square (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (H₀ (R := R)).homologySequenceδ (CochainComplex.mappingCone.triangleh φ) n₀ n₁ h ≫
        (e n₁ K).hom =
      (e n₀ (cone φ)).hom ≫ δ φ n₀ n₁ h := by
  rw [δ, Iso.hom_inv_id_assoc]
  rfl

/-- 三角圏側の短複体 `H^n K → H^n L → H^n (Cone φ)`。 -/
noncomputable abbrev S₂ (n : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _ ((H₀ (R := R)).homologySequence_comp _ (triangleh_distinguished φ) n)

/-- 三角圏側の短複体 `H^{n₀} L → H^{n₀} (Cone φ) → H^{n₁} K`。 -/
noncomputable abbrev S₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _
    ((H₀ (R := R)).comp_homologySequenceδ _ (triangleh_distinguished φ) n₀ n₁ h)

/-- 三角圏側の短複体 `H^{n₀} (Cone φ) → H^{n₁} K → H^{n₁} L`。 -/
noncomputable abbrev S₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk _ _
    ((H₀ (R := R)).homologySequenceδ_comp _ (triangleh_distinguished φ) n₀ n₁ h)

/-- `H^n K → H^n L → H^n (Cone φ)` は完全。 -/
lemma exact₂ (n : ℤ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap φ n)
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) n)
      (comp_eq_zero_transport (S₂ φ n) (e n K) (e n L) (e n (cone φ))
        _ _ (e_naturality n φ)
        (e_naturality n (CochainComplex.mappingCone.inr φ)))).Exact :=
  exact_transport ((H₀ (R := R)).homologySequence_exact₂ _ (triangleh_distinguished φ) n)
    (e n K) (e n L) (e n (cone φ)) _ _ (e_naturality n φ)
    (e_naturality n (CochainComplex.mappingCone.inr φ))

/-- `H^{n₀} L → H^{n₀} (Cone φ) → H^{n₁} K` は完全。 -/
lemma exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) n₀)
      (δ φ n₀ n₁ h)
      (comp_eq_zero_transport (S₃ φ n₀ n₁ h) (e n₀ L) (e n₀ (cone φ))
        (e n₁ K) _ (δ φ n₀ n₁ h)
        (e_naturality n₀ (CochainComplex.mappingCone.inr φ))
        (δ_square φ n₀ n₁ h))).Exact :=
  exact_transport
    ((H₀ (R := R)).homologySequence_exact₃ _ (triangleh_distinguished φ) n₀ n₁ h)
    (e n₀ L) (e n₀ (cone φ)) (e n₁ K) _ (δ φ n₀ n₁ h)
    (e_naturality n₀ (CochainComplex.mappingCone.inr φ)) (δ_square φ n₀ n₁ h)

/-- `H^{n₀} (Cone φ) → H^{n₁} K → H^{n₁} L` は完全。 -/
lemma exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk (δ φ n₀ n₁ h) (HomologicalComplex.homologyMap φ n₁)
      (comp_eq_zero_transport (S₁ φ n₀ n₁ h) (e n₀ (cone φ)) (e n₁ K)
        (e n₁ L) (δ φ n₀ n₁ h) _ (δ_square φ n₀ n₁ h)
        (e_naturality n₁ φ))).Exact :=
  exact_transport
    ((H₀ (R := R)).homologySequence_exact₁ _ (triangleh_distinguished φ) n₀ n₁ h)
    (e n₀ (cone φ)) (e n₁ K) (e n₁ L) (δ φ n₀ n₁ h) _
    (δ_square φ n₀ n₁ h) (e_naturality n₁ φ)

end Cone

end SerrePositivity
