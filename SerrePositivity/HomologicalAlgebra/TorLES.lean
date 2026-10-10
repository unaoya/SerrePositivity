module

public import SerrePositivity.HomologicalAlgebra.ConeResolution
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.Algebra.Exact.Basic

/-!
# `Tor` の長完全列

## 概要

`A` 加群の短完全列 `0 → V₁ →f V₂ →g V₃ → 0` と `A` 代数 `C`（`φ : A →+* C`）に対して、
`Tor_i^A(C, -)`（`TorAlg φ i`）の長完全列

  `… → Tor_{i+1} V₃ → Tor_i V₁ → Tor_i V₂ → Tor_i V₃ → Tor_{i-1} V₁ → … → Tor_0 V₃ → 0`

が存在する（`torAlg_longExact`）。標準的な事実（層 3a）だが Mathlib にはないので、ここで証明する。
論文では Lemma 3.4 の証明（組成列についての帰納法）で、短完全列 `0 → N → V → k → 0` に沿って
正規化長さを比較するのに使う（`IntersectionMultiplicity/NormalizedTor.lean`）。

## 方針

馬蹄補題ではなく写像錐を使う。`f` を分解の間の鎖写像 `f̃` に持ち上げると、その写像錐 `Cone f̃` が
`V₃` の分解になる（`ConeResolution.lean`）。係数拡大 `F = C ⊗_A -` は写像錐と可換なので
`F(Cone f̃) ≅ Cone(F f̃)` であり、写像錐の長完全列（`ConeLES.lean`）

  `H^n(F resV V₁) → H^n(F resV V₂) → H^n(Cone(F f̃)) → H^{n+1}(F resV V₁)`

を、`Tor_i(V_k) ≅ H^{-i}(F(V_k の分解))`（`Tor.lean` の `torIsoCochain`）で `Tor` の言葉に移せば、
求める長完全列になる。`Tor_0 V₂ → Tor_0 V₃` の全射性は、長完全列の次の項 `H^1(F resV V₁)` が零で
あることから出る。

## 注意

長完全列の射 `α`、`β`、`δ` は分解の上で構成したもので、`Tor` の関手性で与えられる射と一致する
はずだが、その一致はここでは示さない。Lemma 3.4 では完全性だけを使う。また主定理
`torAlg_longExact` は `∃ α β δ, …` の形で述べる。利用者は射の具体形に依存しないので、この形で
十分である。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

namespace TorLES

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)
variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  [AddCommGroup V₃] [Module A V₃]
variable (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f)
  (hg : Function.Surjective g) (hfg : Function.Exact f g)

/-- 持ち上げ `f̃ : resV V₁ ⟶ resV V₂`（`liftSES f`）に係数拡大 `F = C ⊗_A -` を施した鎖写像 `F f̃`。
この写像錐の長完全列が `Tor` の長完全列になる。 -/
noncomputable abbrev ψ : baseChange φ (resV A V₁) ⟶ baseChange φ (resV A V₂) :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex _).map (liftSES f)

/-- `Tor_i^A(C, V₁)` と、`V₁` の分解を係数拡大した複体の `-i` 次ホモロジーの同型（`torIsoCochain`）。 -/
noncomputable abbrev T₁ (i : ℕ) :=
  torIsoCochain φ (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))) i

/-- `Tor_i^A(C, V₂)` と、`V₂` の分解を係数拡大した複体の `-i` 次ホモロジーの同型（`torIsoCochain`）。 -/
noncomputable abbrev T₂ (i : ℕ) :=
  torIsoCochain φ (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₂))) i

/-- `Tor_i^A(C, V₃)` と、`Cone f̃`（`V₃` の分解、`isResolutionOf_cone`）を係数拡大した複体の `-i` 次
ホモロジーの同型（`torIsoCochain`）。 -/
noncomputable abbrev T₃ (i : ℕ) :=
  torIsoCochain φ (isResolutionOf_cone f g hf hg hfg) i

/-- 係数拡大と写像錐の可換性 `F(Cone f̃) ≅ Cone(F f̃)`（Mathlib の
`homotopyCofiber.mapHomologicalComplexObjIso`）。加法的関手は写像錐を写像錐に送る。 -/
noncomputable abbrev cIso : baseChange φ (Cone.cone (liftSES f)) ≅ Cone.cone (ψ φ f) :=
  HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso (liftSES f)
    (ModuleCat.extendScalars.{u, u, u} φ)

/-- `cIso` がホモロジーに誘導する同型 `H^n(F(Cone f̃)) ≅ H^n(Cone(F f̃))`。`T₃` の右辺と写像錐の
長完全列の項をつなぐ。 -/
noncomputable abbrev cH (n : ℤ) :
    (baseChange φ (Cone.cone (liftSES f))).homology n ≅ (Cone.cone (ψ φ f)).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cIso φ f)

/-- `α_i : Tor_i V₁ → Tor_i V₂`。同一視 `T₁`、`T₂` のもとで、`F f̃` が `-i` 次ホモロジーに誘導する射。 -/
noncomputable def α (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₁) ⟶
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₂) :=
  (T₁ φ (V₁ := V₁) i).hom ≫ HomologicalComplex.homologyMap (ψ φ f) (-(i : ℤ)) ≫ (T₂ φ i).inv

/-- `β_i : Tor_i V₂ → Tor_i V₃`。同一視 `T₂`、`T₃`（と `cH`）のもとで、写像錐への埋め込み
`inr(F f̃)` が `-i` 次ホモロジーに誘導する射。 -/
noncomputable def β (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₂) ⟶
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₃) :=
  (T₂ φ (V₂ := V₂) i).hom ≫
    HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (ψ φ f)) (-(i : ℤ)) ≫
    (cH φ f (-(i : ℤ))).inv ≫ (T₃ φ f g hf hg hfg i).inv

/-- 連結射 `δ_i : Tor_{i+1} V₃ → Tor_i V₁`。同一視のもとで、写像錐の長完全列の連結射 `Cone.δ`
（`H^{-(i+1)}(Cone(F f̃)) → H^{-i}(F resV V₁)`）。 -/
noncomputable def δ (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived (i + 1)).obj (ModuleCat.of A V₃) ⟶
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (ModuleCat.of A V₁) :=
  (T₃ φ f g hf hg hfg (i + 1)).hom ≫ (cH φ f (-((i + 1 : ℕ) : ℤ))).hom ≫
    Cone.δ (ψ φ f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by push_cast; ring) ≫ (T₁ φ i).inv

/-- `Tor_i V₁ →α Tor_i V₂ →β Tor_i V₃` は完全。写像錐の長完全列の中央部分 `Cone.exact₂` を、同型
`T₁`、`T₂`、`T₃ ∘ cH` に沿って移す（`exact_transport`）。 -/
lemma exact_αβ (i : ℕ) : Function.Exact (α φ f i).hom (β φ f g hf hg hfg i).hom := by
  have h := exact_transport (Cone.exact₂ (ψ φ f) (-(i : ℤ))) (T₁ φ i).symm (T₂ φ i).symm
    ((cH φ f _).symm ≪≫ (T₃ φ f g hf hg hfg i).symm) (α φ f i) (β φ f g hf hg hfg i)
    (by simp [α]) (by simp [β])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `Tor_{i+1} V₂ →β Tor_{i+1} V₃ →δ Tor_i V₁` は完全。写像錐の長完全列の `Cone.exact₃` を同型で移す。 -/
lemma exact_βδ (i : ℕ) :
    Function.Exact (β φ f g hf hg hfg (i + 1)).hom (δ φ f g hf hg hfg i).hom := by
  have h := exact_transport (Cone.exact₃ (ψ φ f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ))
      (by push_cast; ring))
    (T₂ φ (i + 1)).symm ((cH φ f _).symm ≪≫ (T₃ φ f g hf hg hfg (i + 1)).symm) (T₁ φ i).symm
    (β φ f g hf hg hfg (i + 1)) (δ φ f g hf hg hfg i) (by simp [β])
    (by simp only [δ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `Tor_{i+1} V₃ →δ Tor_i V₁ →α Tor_i V₂` は完全。写像錐の長完全列の `Cone.exact₁` を同型で移す。 -/
lemma exact_δα (i : ℕ) : Function.Exact (δ φ f g hf hg hfg i).hom (α φ f i).hom := by
  have h := exact_transport (Cone.exact₁ (ψ φ f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ))
      (by push_cast; ring))
    ((cH φ f _).symm ≪≫ (T₃ φ f g hf hg hfg (i + 1)).symm) (T₁ φ i).symm (T₂ φ i).symm
    (δ φ f g hf hg hfg i) (α φ f i)
    (by simp only [δ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
    (by simp [α])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `β_0 : Tor_0 V₂ → Tor_0 V₃` は全射。長完全列の次の項 `H^1(F resV V₁)` が零（分解は正の次数で
零）なので、`Cone.exact₃` から `inr` の誘導する射が全射（epi）になることによる。 -/
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

/-- **Tor の長完全列**：短完全列 `0 → V₁ →f V₂ →g V₃ → 0` に対して、`C` 線形写像の族
`α_i : Tor_i V₁ → Tor_i V₂`、`β_i : Tor_i V₂ → Tor_i V₃`、`δ_i : Tor_{i+1} V₃ → Tor_i V₁` があって、
`α_i, β_i`、`β_{i+1}, δ_i`、`δ_i, α_i` の各所で完全であり、`β_0` は全射。`TorLES` 名前空間で
構成した射と完全性をまとめたもの。 -/
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
