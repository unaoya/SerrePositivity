module

public import SerrePositivity.Descent.ConeResolution
public import SerrePositivity.KoszulBaseChange
public import SerrePositivity.TorCochain
public import Mathlib.Algebra.Exact.Basic

/-!
# `Tor` の長完全列（層 3a）

`A` 加群の短完全列 `0 → V₁ →f V₂ →g V₃ → 0` に対して、`Tor_i^A(-, C)`（`TorAlg φ i`）の長完全列

  `… → Tor_{i+1} V₃ → Tor_i V₁ → Tor_i V₂ → Tor_i V₃ → Tor_{i-1} V₁ → … → Tor_0 V₃ → 0`

がある。

証明は馬蹄補題ではなく写像錐による：`V₁`、`V₂` の射影分解（ℤ 添字に延長）の間の `f` の持ち上げ
`f̃` の錐 `Cone f̃` が `V₃` の分解になる（`isResolutionOf_cone`）。係数拡大 `F = C ⊗_A -` は
錐と両立するので、`F f̃` の錐の長完全列（`Cone.exact₁₂₃`）を `Tor_i V_k ≅ H^{-i}(F K_k)`
（`torIsoCochain`）で移せば Tor の長完全列になる。長完全列の射は `Tor` の関手性で与えられる
ものと一致するはずだが、ここではその一致は主張しない（Lemma 3.4 では完全性だけを使う）。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

/-- 項が零ならホモロジーも零。 -/
lemma isZero_homology_of_isZero_X {C : Type*} [Category* C] [Abelian C] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι) (h : IsZero (K.X i)) :
    IsZero (K.homology i) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (ShortComplex.exact_of_isZero_X₂ _ h)

namespace TorLES

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  [AddCommGroup V₃] [Module A V₃]
variable (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f)
  (hg : Function.Surjective g) (hfg : Function.Exact f g)

/-- `F f̃`。 -/
noncomputable abbrev ψ : baseChange φ (resV A V₁) ⟶ baseChange φ (resV A V₂) :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (liftSES f)

/-- `Tor_i V₁ ≅ H^{-i}(F (resV V₁))`。 -/
noncomputable abbrev T₁ (i : ℕ) :=
  torIsoCochain φ (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))) i

/-- `Tor_i V₂ ≅ H^{-i}(F (resV V₂))`。 -/
noncomputable abbrev T₂ (i : ℕ) :=
  torIsoCochain φ (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₂))) i

/-- `Tor_i V₃ ≅ H^{-i}(F (Cone f̃))`。 -/
noncomputable abbrev T₃ (i : ℕ) :=
  torIsoCochain φ (isResolutionOf_cone f g hf hg hfg) i

/-- `F (Cone f̃) ≅ Cone (F f̃)`。 -/
noncomputable abbrev cIso : baseChange φ (Cone.cone (liftSES f)) ≅ Cone.cone (ψ φ f) :=
  HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso (liftSES f)
    (ModuleCat.extendScalars.{u, u, u} φ)

/-- `cIso` のホモロジー。 -/
noncomputable abbrev cH (n : ℤ) :
    (baseChange φ (Cone.cone (liftSES f))).homology n ≅ (Cone.cone (ψ φ f)).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cIso φ f)

/-- `α_i : Tor_i V₁ → Tor_i V₂`。 -/
noncomputable def α (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₁) ⟶
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₂) :=
  (T₁ φ (V₁ := V₁) i).hom ≫ HomologicalComplex.homologyMap (ψ φ f) (-(i : ℤ)) ≫ (T₂ φ i).inv

/-- `β_i : Tor_i V₂ → Tor_i V₃`。 -/
noncomputable def β (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₂) ⟶
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₃) :=
  (T₂ φ (V₂ := V₂) i).hom ≫
    HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (ψ φ f)) (-(i : ℤ)) ≫
    (cH φ f (-(i : ℤ))).inv ≫ (T₃ φ f g hf hg hfg i).inv

/-- `δ_i : Tor_{i+1} V₃ → Tor_i V₁`。 -/
noncomputable def δ (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)).obj (ModuleCat.of A V₃) ⟶
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₁) :=
  (T₃ φ f g hf hg hfg (i + 1)).hom ≫ (cH φ f (-((i + 1 : ℕ) : ℤ))).hom ≫
    Cone.δ (ψ φ f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by push_cast; ring) ≫ (T₁ φ i).inv

/-- `Tor_i V₁ → Tor_i V₂ → Tor_i V₃` は完全。 -/
lemma exact_αβ (i : ℕ) : Function.Exact (α φ f i).hom (β φ f g hf hg hfg i).hom := by
  have h := exact_transport (Cone.exact₂ (ψ φ f) (-(i : ℤ))) (T₁ φ i).symm (T₂ φ i).symm
    ((cH φ f _).symm ≪≫ (T₃ φ f g hf hg hfg i).symm) (α φ f i) (β φ f g hf hg hfg i)
    (by simp [α]) (by simp [β])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `Tor_{i+1} V₂ → Tor_{i+1} V₃ → Tor_i V₁` は完全。 -/
lemma exact_βδ (i : ℕ) :
    Function.Exact (β φ f g hf hg hfg (i + 1)).hom (δ φ f g hf hg hfg i).hom := by
  have h := exact_transport (Cone.exact₃ (ψ φ f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ))
      (by push_cast; ring))
    (T₂ φ (i + 1)).symm ((cH φ f _).symm ≪≫ (T₃ φ f g hf hg hfg (i + 1)).symm) (T₁ φ i).symm
    (β φ f g hf hg hfg (i + 1)) (δ φ f g hf hg hfg i) (by simp [β])
    (by simp only [δ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `Tor_{i+1} V₃ → Tor_i V₁ → Tor_i V₂` は完全。 -/
lemma exact_δα (i : ℕ) : Function.Exact (δ φ f g hf hg hfg i).hom (α φ f i).hom := by
  have h := exact_transport (Cone.exact₁ (ψ φ f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ))
      (by push_cast; ring))
    ((cH φ f _).symm ≪≫ (T₃ φ f g hf hg hfg (i + 1)).symm) (T₁ φ i).symm (T₂ φ i).symm
    (δ φ f g hf hg hfg i) (α φ f i)
    (by simp only [δ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
    (by simp [α])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `Tor_0 V₂ → Tor_0 V₃` は全射。 -/
lemma surjective_β_zero : Function.Surjective (β φ f g hf hg hfg 0).hom := by
  have hz : IsZero ((baseChange φ (resV A V₁)).homology (-((0 : ℕ) : ℤ) + 1)) :=
    isZero_homology_of_isZero_X _ _ (baseChange_isZero_X_of_pos φ _
      (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))).isZero_X _ (by simp))
  have hepi : Epi (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (ψ φ f))
      (-((0 : ℕ) : ℤ))) :=
    (Cone.exact₃ (ψ φ f) (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) rfl).epi_f (hz.eq_zero_of_tgt _)
  have : Epi (β φ f g hf hg hfg 0) := by
    unfold β
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).mp this

end TorLES

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- **Tor の長完全列**。 -/
theorem torAlg_longExact {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
    (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    ∃ (α : ∀ i : ℕ, TorAlg φ i V₁ →ₗ[C] TorAlg φ i V₂)
      (β : ∀ i : ℕ, TorAlg φ i V₂ →ₗ[C] TorAlg φ i V₃)
      (δ : ∀ i : ℕ, TorAlg φ (i + 1) V₃ →ₗ[C] TorAlg φ i V₁),
      (∀ i, Function.Exact (α i) (β i)) ∧ (∀ i, Function.Exact (β (i + 1)) (δ i)) ∧
        (∀ i, Function.Exact (δ i) (α i)) ∧ Function.Surjective (β 0) :=
  ⟨fun i ↦ (TorLES.α φ f i).hom, fun i ↦ (TorLES.β φ f g hf hg hfg i).hom,
    fun i ↦ (TorLES.δ φ f g hf hg hfg i).hom, TorLES.exact_αβ φ f g hf hg hfg,
    TorLES.exact_βδ φ f g hf hg hfg, TorLES.exact_δα φ f g hf hg hfg,
    TorLES.surjective_β_zero φ f g hf hg hfg⟩

end SerrePositivity
