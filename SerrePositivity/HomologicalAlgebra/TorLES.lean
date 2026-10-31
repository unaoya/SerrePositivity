module

public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# 左導来関手と `Tor` の長完全列

加群圏の間の任意の加法的関手 `G` に対し、短完全列から左導来関手の長完全列を構成する。
Mathlib の `Functor.leftDerived` をそのまま使い、分解の持ち上げ、写像錐の分解、
加法的関手と写像錐の可換性、ホモロジーの長完全列を組み合わせる。

`leftDerived_longExact` が一般定理であり、通常のテンソル関手への適用が
`torModule_longExact`、係数拡大関手への適用が `torAlg_longExact` である。
`torModule_longExact_left` は第2変数の射影分解と平坦性を用いて、第1変数の長完全列も与える。
Noether 性、正則性、有限生成性は仮定しない。

ここでは、構成した射について完全性と末端の全射性を証明する。
第2変数の `α` と第1変数の `α`・`β` は、導来関手の標準の射に一致する。
第2変数の `β` の同定と、連結射の自然性はまだ示していない。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

namespace LeftDerivedLES

variable {A C : Type u} [CommRing A] [CommRing C]
  (G : ModuleCat.{u} A ⥤ ModuleCat.{u} C) [G.Additive]
variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  [AddCommGroup V₃] [Module A V₃]
variable (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f)
  (hg : Function.Surjective g) (hfg : Function.Exact f g)

/-- 短完全列の単射を射影分解の間に持ち上げ、加法的関手 `G` を各項に施した鎖写像。 -/
noncomputable abbrev ψ :
    (G.mapHomologicalComplex _).obj (resV A V₁) ⟶
      (G.mapHomologicalComplex _).obj (resV A V₂) :=
  (G.mapHomologicalComplex _).map (liftSES f)

/-- `LᵢG(V₁)` を、`V₁` の標準射影分解に `G` を施した複体のホモロジーと同一視する。 -/
noncomputable abbrev T₁ (i : ℕ) :=
  leftDerivedIsoCochain G (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))) i

/-- `LᵢG(V₂)` を、`V₂` の標準射影分解に `G` を施した複体のホモロジーと同一視する。 -/
noncomputable abbrev T₂ (i : ℕ) :=
  leftDerivedIsoCochain G (isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₂))) i

/-- `LᵢG(V₃)` を、持ち上げの写像錐に `G` を施した複体のホモロジーと同一視する。 -/
noncomputable abbrev T₃ (i : ℕ) :=
  leftDerivedIsoCochain G (isResolutionOf_cone f g hf hg hfg) i

/-- 加法的関手と写像錐の可換性。Mathlib の `homotopyCofiber.mapHomologicalComplexObjIso` を使う。 -/
noncomputable abbrev cIso :
    (G.mapHomologicalComplex _).obj (Cone.cone (liftSES f)) ≅ Cone.cone (ψ G f) :=
  HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso (liftSES f)
    G

/-- 加法的関手と写像錐の比較同型がホモロジーに誘導する同型。 -/
noncomputable abbrev cH (n : ℤ) :
    ((G.mapHomologicalComplex _).obj (Cone.cone (liftSES f))).homology n ≅
      (Cone.cone (ψ G f)).homology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (cIso G f)

/-- 長完全列の射 `αᵢ : LᵢG(V₁) → LᵢG(V₂)`。分解の間の持ち上げが誘導する射で構成する。 -/
noncomputable def α (i : ℕ) :
    (G.leftDerived i).obj (ModuleCat.of A V₁) ⟶
      (G.leftDerived i).obj (ModuleCat.of A V₂) :=
  (T₁ G (V₁ := V₁) i).hom ≫ HomologicalComplex.homologyMap (ψ G f) (-(i : ℤ)) ≫ (T₂ G i).inv

/-- 分解の持ち上げから作った `α` は、左導来関手の標準の射である。 -/
lemma α_eq_map (i : ℕ) : α G f i = (G.leftDerived i).map (ModuleCat.ofHom f) := by
  apply (cancel_mono (T₂ G (V₂ := V₂) i).hom).mp
  simp only [α, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (leftDerivedIsoCochain_hom_naturality G _ _ (liftSES f) (ModuleCat.ofHom f)
    (extLift_homologyZero _ _ _) i).symm

/-- 長完全列の射 `βᵢ : LᵢG(V₂) → LᵢG(V₃)`。写像錐への埋め込みが誘導する射で構成する。 -/
noncomputable def β (i : ℕ) :
    (G.leftDerived i).obj (ModuleCat.of A V₂) ⟶
      (G.leftDerived i).obj (ModuleCat.of A V₃) :=
  (T₂ G (V₂ := V₂) i).hom ≫
    HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (ψ G f)) (-(i : ℤ)) ≫
    (cH G f (-(i : ℤ))).inv ≫ (T₃ G f g hf hg hfg i).inv

/-- 連結射 `δᵢ : Lᵢ₊₁G(V₃) → LᵢG(V₁)`。写像錐のホモロジーの連結射から構成する。 -/
noncomputable def δ (i : ℕ) :
    (G.leftDerived (i + 1)).obj (ModuleCat.of A V₃) ⟶
      (G.leftDerived i).obj (ModuleCat.of A V₁) :=
  (T₃ G f g hf hg hfg (i + 1)).hom ≫ (cH G f (-((i + 1 : ℕ) : ℤ))).hom ≫
    Cone.δ (ψ G f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by push_cast; ring) ≫ (T₁ G i).inv

/-- `αᵢ` と `βᵢ` の位置での完全性。写像錐の長完全列を分解による計算同型で移す。 -/
lemma exact_αβ (i : ℕ) : Function.Exact (α G f i).hom (β G f g hf hg hfg i).hom := by
  have h := exact_transport (Cone.exact₂ (ψ G f) (-(i : ℤ))) (T₁ G i).symm (T₂ G i).symm
    ((cH G f _).symm ≪≫ (T₃ G f g hf hg hfg i).symm) (α G f i) (β G f g hf hg hfg i)
    (by simp [α]) (by simp [β])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `βᵢ₊₁` と `δᵢ` の位置での完全性。写像錐の長完全列を分解による計算同型で移す。 -/
lemma exact_βδ (i : ℕ) :
    Function.Exact (β G f g hf hg hfg (i + 1)).hom (δ G f g hf hg hfg i).hom := by
  have h := exact_transport (Cone.exact₃ (ψ G f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ))
      (by push_cast; ring))
    (T₂ G (i + 1)).symm ((cH G f _).symm ≪≫ (T₃ G f g hf hg hfg (i + 1)).symm) (T₁ G i).symm
    (β G f g hf hg hfg (i + 1)) (δ G f g hf hg hfg i) (by simp [β])
    (by simp only [δ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- `δᵢ` と `αᵢ` の位置での完全性。写像錐の長完全列を分解による計算同型で移す。 -/
lemma exact_δα (i : ℕ) : Function.Exact (δ G f g hf hg hfg i).hom (α G f i).hom := by
  have h := exact_transport (Cone.exact₁ (ψ G f) (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ))
      (by push_cast; ring))
    ((cH G f _).symm ≪≫ (T₃ G f g hf hg hfg (i + 1)).symm) (T₁ G i).symm (T₂ G i).symm
    (δ G f g hf hg hfg i) (α G f i)
    (by simp only [δ, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc])
    (by simp [α])
  rw [LinearMap.exact_iff]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h).symm

/-- 末端の射 `β₀` は全射。射影分解は正の次数で零なので、その次のホモロジーが消える。 -/
lemma surjective_β_zero : Function.Surjective (β G f g hf hg hfg 0).hom := by
  have hz : IsZero (((G.mapHomologicalComplex _).obj (resV A V₁)).homology (-((0 : ℕ) : ℤ) + 1)) :=
    isZero_homology_of_isZero_X _ _ (G.map_isZero
      ((isResolutionOf_extRes (projectiveResolution (ModuleCat.of A V₁))).isZero_X _ (by simp)))
  have hepi : Epi (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (ψ G f))
      (-((0 : ℕ) : ℤ))) :=
    (Cone.exact₃ (ψ G f) (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) rfl).epi_f (hz.eq_zero_of_tgt _)
  have : Epi (β G f g hf hg hfg 0) := by
    unfold β
    infer_instance
  exact (ModuleCat.epi_iff_surjective _).mp this

end LeftDerivedLES

variable {A C : Type u} [CommRing A] [CommRing C]
  (G : ModuleCat.{u} A ⥤ ModuleCat.{u} C) [G.Additive]

/-- 加法的関手の左導来関手の長完全列。加群の短完全列に対して、
射影分解の持ち上げと写像錐から射と連結射を構成する。右完全性や有限性の仮定は不要である。
通常の Tor と代数係数の Tor に共通して適用する。 -/
theorem leftDerived_longExact {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
    (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    ∃ (α : ∀ i : ℕ, (G.leftDerived i).obj (ModuleCat.of A V₁) →ₗ[C]
        (G.leftDerived i).obj (ModuleCat.of A V₂))
      (β : ∀ i : ℕ, (G.leftDerived i).obj (ModuleCat.of A V₂) →ₗ[C]
        (G.leftDerived i).obj (ModuleCat.of A V₃))
      (δ : ∀ i : ℕ, (G.leftDerived (i + 1)).obj (ModuleCat.of A V₃) →ₗ[C]
        (G.leftDerived i).obj (ModuleCat.of A V₁)),
      (∀ i, Function.Exact (α i) (β i)) ∧ (∀ i, Function.Exact (β (i + 1)) (δ i)) ∧
        (∀ i, Function.Exact (δ i) (α i)) ∧ Function.Surjective (β 0) :=
  ⟨fun i ↦ (LeftDerivedLES.α G f i).hom, fun i ↦ (LeftDerivedLES.β G f g hf hg hfg i).hom,
    fun i ↦ (LeftDerivedLES.δ G f g hf hg hfg i).hom, LeftDerivedLES.exact_αβ G f g hf hg hfg,
    LeftDerivedLES.exact_βδ G f g hf hg hfg, LeftDerivedLES.exact_δα G f g hf hg hfg,
    LeftDerivedLES.surjective_β_zero G f g hf hg hfg⟩


variable (φ : A →+* C)

/-- 係数拡大関手に対する Tor の長完全列。一般の左導来関手の長完全列を適用する。 -/
theorem torAlg_longExact {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
    (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    ∃ (α : ∀ i : ℕ, TorAlg φ i V₁ →ₗ[C] TorAlg φ i V₂)
      (β : ∀ i : ℕ, TorAlg φ i V₂ →ₗ[C] TorAlg φ i V₃)
      (δ : ∀ i : ℕ, TorAlg φ (i + 1) V₃ →ₗ[C] TorAlg φ i V₁),
      (∀ i, Function.Exact (α i) (β i)) ∧ (∀ i, Function.Exact (β (i + 1)) (δ i)) ∧
        (∀ i, Function.Exact (δ i) (α i)) ∧ Function.Surjective (β 0) :=
  leftDerived_longExact (ModuleCat.extendScalars φ) f g hf hg hfg

/-- 任意の加群 `M` に対する `Tor_i^A(M, -)` の長完全列。
第1変数に代数構造を要求せず、Mathlib のテンソル関手の左導来関手として得る。 -/
theorem torModule_longExact (M : Type u) [AddCommGroup M] [Module A M]
    {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
    [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
    (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    ∃ (α : ∀ i : ℕ, TorModule A i M V₁ →ₗ[A] TorModule A i M V₂)
      (β : ∀ i : ℕ, TorModule A i M V₂ →ₗ[A] TorModule A i M V₃)
      (δ : ∀ i : ℕ, TorModule A (i + 1) M V₃ →ₗ[A] TorModule A i M V₁),
      (∀ i, Function.Exact (α i) (β i)) ∧ (∀ i, Function.Exact (β (i + 1)) (δ i)) ∧
        (∀ i, Function.Exact (δ i) (α i)) ∧ Function.Surjective (β 0) :=
  leftDerived_longExact
    ((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M))
    f g hf hg hfg

section leftVariable

set_option backward.isDefEq.respectTransparency false

open MonoidalCategory

variable {R : Type u} [CommRing R]

/-- 固定した複体 `P` に対し、加群 `M` を各項でテンソルした複体 `M ⊗ P` に送る関手。 -/
noncomputable def tensorComplexFunctor (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj M := ((tensorLeft M).mapHomologicalComplex _).obj P
  map f := (NatTrans.mapHomologicalComplex ((tensoringLeft _).map f) _).app P
  map_id M := by ext i; simp
  map_comp f g := by ext i; simp
/-- 複体とのテンソル関手は零射を保つ。 -/
instance (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorComplexFunctor P).PreservesZeroMorphisms where
  map_zero X Y := by
    ext i x
    change (TensorProduct.map (0 : X →ₗ[R] Y) LinearMap.id) x = 0
    simp

/-- 各項が平坦な複体とのテンソルは、加群の短完全列を複体の短完全列に送る。
完全性は各次数で判定し、Mathlib の平坦加群とのテンソルの完全性を用いる。 -/
theorem tensorComplex_shortExact (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, Module.Flat R (P.X i))
    (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact) :
    (S.map (tensorComplexFunctor P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hp i
  change (S.map (tensorRight (P.X i))).ShortExact
  have := hs.mono_f
  have := hs.epi_g
  refine {
    exact := Module.Flat.rTensor_shortComplex_exact _ S hs.exact
    mono_f := ?_
    epi_g := ?_ }
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact Module.Flat.rTensor_preserves_injective_linearMap S.f.hom
      ((ModuleCat.mono_iff_injective _).mp hs.mono_f)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.rTensor_surjective _ ((ModuleCat.epi_iff_surjective _).mp hs.epi_g)

/-- 第1変数の短完全列から得られる通常の Tor の長完全列。
第2変数の射影分解を固定し、その各項の平坦性によって複体の短完全列を作る。
Mathlib のホモロジー長完全列を分解による計算同型で移送する。正則性・有限生成性は不要である。 -/
theorem torModule_longExact_left_with_maps (N : Type u) [AddCommGroup N] [Module R N]
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g) :
    ∃ (α : ∀ i : ℕ, TorModule R i M₁ N →ₗ[R] TorModule R i M₂ N)
      (β : ∀ i : ℕ, TorModule R i M₂ N →ₗ[R] TorModule R i M₃ N)
      (δ : ∀ i : ℕ, TorModule R (i + 1) M₃ N →ₗ[R] TorModule R i M₁ N),
      (∀ i, Function.Exact (α i) (β i)) ∧
      (∀ i, Function.Exact (β (i + 1)) (δ i)) ∧
      (∀ i, Function.Exact (δ i) (α i)) ∧ Function.Surjective (β 0) ∧
      (∀ i, α i =
        (((Tor (ModuleCat R) i).map (ModuleCat.ofHom f)).app (ModuleCat.of R N)).hom) ∧
      (∀ i, β i =
        (((Tor (ModuleCat R) i).map (ModuleCat.ofHom g)).app (ModuleCat.of R N)).hom) := by
  let P := resV R N
  let S := ModuleCat.shortComplexOfCompEqZero f g
    (LinearMap.ext (fun x => he.apply_apply_eq_zero x))
  have hs : S.ShortExact := ModuleCat.shortComplex_shortExact S he hf hg
  let T := S.map (tensorComplexFunctor P)
  have ht : T.ShortExact := tensorComplex_shortExact P (fun i => by
    have := (isResolutionOf_extRes (projectiveResolution (ModuleCat.of R N))).projective i
    infer_instance) S hs
  let e (M : ModuleCat.{u} R) (i : ℕ) :=
    torModuleIsoCochain M (isResolutionOf_extRes (projectiveResolution (ModuleCat.of R N))) i
  let α (i : ℕ) := (e (ModuleCat.of R M₁) i).hom ≫
    HomologicalComplex.homologyMap T.f (-(i : ℤ)) ≫ (e (ModuleCat.of R M₂) i).inv
  let β (i : ℕ) := (e (ModuleCat.of R M₂) i).hom ≫
    HomologicalComplex.homologyMap T.g (-(i : ℤ)) ≫ (e (ModuleCat.of R M₃) i).inv
  let δ (i : ℕ) := (e (ModuleCat.of R M₃) (i + 1)).hom ≫
    ht.δ (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by
      change -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ)
      omega) ≫ (e (ModuleCat.of R M₁) i).inv
  refine ⟨fun i => (α i).hom, fun i => (β i).hom, fun i => (δ i).hom,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h := exact_transport (ht.homology_exact₂ (-(i : ℤ)))
      (e (ModuleCat.of R M₁) i).symm (e (ModuleCat.of R M₂) i).symm
      (e (ModuleCat.of R M₃) i).symm (α i) (β i)
      (by simp only [α, Iso.symm_hom, Iso.inv_hom_id_assoc])
      (by simp only [β, Iso.symm_hom, Iso.inv_hom_id_assoc])
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h
  · intro i
    have h := exact_transport (ht.homology_exact₃ (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by
      change -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ)
      omega))
      (e (ModuleCat.of R M₂) (i + 1)).symm (e (ModuleCat.of R M₃) (i + 1)).symm
      (e (ModuleCat.of R M₁) i).symm (β (i + 1)) (δ i)
      (by simp only [β, Iso.symm_hom, Iso.inv_hom_id_assoc])
      (by simp only [δ, Iso.symm_hom, Iso.inv_hom_id_assoc])
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h
  · intro i
    have h := exact_transport (ht.homology_exact₁ (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) (by
      change -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ)
      omega))
      (e (ModuleCat.of R M₃) (i + 1)).symm (e (ModuleCat.of R M₁) i).symm
      (e (ModuleCat.of R M₂) i).symm (δ i) (α i)
      (by simp only [δ, Iso.symm_hom, Iso.inv_hom_id_assoc])
      (by simp only [α, Iso.symm_hom, Iso.inv_hom_id_assoc])
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h
  · have hz : IsZero (T.X₁.homology (-(0 : ℤ) + 1)) :=
      isZero_homology_of_isZero_X _ _ ((tensorLeft (ModuleCat.of R M₁)).map_isZero
        ((isResolutionOf_extRes (projectiveResolution (ModuleCat.of R N))).isZero_X _ (by simp)))
    have : Epi (HomologicalComplex.homologyMap T.g (-(0 : ℤ))) :=
      (ht.homology_exact₃ (-(0 : ℤ)) (-(0 : ℤ) + 1) rfl).epi_f (hz.eq_zero_of_tgt _)
    have : Epi (β 0) := by unfold β; infer_instance
    exact (ModuleCat.epi_iff_surjective _).mp this
  · intro i
    apply congrArg ModuleCat.Hom.hom
    apply (cancel_mono (e (ModuleCat.of R M₂) i).hom).mp
    simp only [α, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (leftDerivedIsoCochain_natTrans _ _ ((tensoringLeft _).map (ModuleCat.ofHom f)) _ i).symm
  · intro i
    apply congrArg ModuleCat.Hom.hom
    apply (cancel_mono (e (ModuleCat.of R M₃) i).hom).mp
    simp only [β, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (leftDerivedIsoCochain_natTrans _ _ ((tensoringLeft _).map (ModuleCat.ofHom g)) _ i).symm

/-- 第1変数の Tor 長完全列。標準の射との一致を含む版から完全性を取り出す。 -/
theorem torModule_longExact_left (N : Type u) [AddCommGroup N] [Module R N]
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g) :
    ∃ (α : ∀ i : ℕ, TorModule R i M₁ N →ₗ[R] TorModule R i M₂ N)
      (β : ∀ i : ℕ, TorModule R i M₂ N →ₗ[R] TorModule R i M₃ N)
      (δ : ∀ i : ℕ, TorModule R (i + 1) M₃ N →ₗ[R] TorModule R i M₁ N),
      (∀ i, Function.Exact (α i) (β i)) ∧
      (∀ i, Function.Exact (β (i + 1)) (δ i)) ∧
      (∀ i, Function.Exact (δ i) (α i)) ∧ Function.Surjective (β 0) := by
  obtain ⟨α, β, δ, hab, hbd, hda, hb, _, _⟩ :=
    torModule_longExact_left_with_maps N f g hf hg he
  exact ⟨α, β, δ, hab, hbd, hda, hb⟩

end leftVariable

end SerrePositivity
