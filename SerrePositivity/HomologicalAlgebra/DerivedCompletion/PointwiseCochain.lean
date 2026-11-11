module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseExact
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import SerrePositivity.HomologicalAlgebra.PowerTorsionDerivedDescent
public import SerrePositivity.HomologicalAlgebra.MapExtend
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange

/-!
# 正則な各項を持つ複体の H⁰ 完備化

## 概要
指定スカラーが各項で正則な複体の擬同型は、各項の H⁰ 主完備化で擬同型に移る。

## 方針
非輪状な正則複体をサイクルの短完全列に分け、両端の正則性で完備化後も短完全にする。
写像錐と加法的な関手の比較で、擬同型の主張を得る。

## 規約
添字は整数。基底環の正則性・有限性・平坦性、有界性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4 の各項を完備化した係数変更の擬同型。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace SerrePositivity.DerivedCompletion

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (a : R)
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

private abbrev completionCycle (i : ℤ) := LinearMap.ker (K.d i (i + 1)).hom

private def completionCycleProjection (i : ℤ) : K.X i →ₗ[R] completionCycle K (i + 1) :=
  (K.d i (i + 1)).hom.codRestrict _ (fun x => by
    change K.d (i + 1) ((i + 1) + 1) (K.d i (i + 1) x) = 0
    exact ConcreteCategory.congr_hom (K.d_comp_d i (i + 1) ((i + 1) + 1)) x)

private def completionCycleSequence (i : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (completionCycle K i).subtype
    (completionCycleProjection K i) (by
      ext x
      exact x.property)

private theorem completionCycle_regular
    (hr : ∀ i, IsSMulRegular (K.X i) a) (i : ℤ) : IsSMulRegular (completionCycle K i) a := by
  intro x y h
  apply Subtype.ext
  exact hr i (congrArg Subtype.val h)

private theorem completionCycleSequence_shortExact (hK : K.Acyclic) (i : ℤ) :
    (completionCycleSequence K i).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      exact congrArg Subtype.val hx
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      exact x.property
  · exact (completionCycle K i).injective_subtype
  · intro y
    have he : (K.sc' i (i + 1) ((i + 1) + 1)).Exact :=
      (K.exactAt_iff' i (i + 1) ((i + 1) + 1) (by simp) (by simp)).mp (hK (i + 1))
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp he y.val y.property
    exact ⟨x, Subtype.ext hx⟩

private theorem completionCycleSequence_factor (i : ℤ) :
    (completionCycleSequence K i).g ≫ (completionCycleSequence K (i + 1)).f =
      K.d i (i + 1) := by
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem map_acyclic_of_cycle_sequences (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] (hs : ∀ i, ((completionCycleSequence K i).map F).ShortExact) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  let FK := (F.mapHomologicalComplex (.up ℤ)).obj K
  have hd (i : ℤ) : F.map (K.d i (i + 1)) =
      F.map (completionCycleSequence K i).g ≫ F.map (completionCycleSequence K (i + 1)).f := by
    rw [← Functor.map_comp, completionCycleSequence_factor]
  have hex (i : ℤ) : FK.ExactAt (i + 1) := by
    apply (FK.exactAt_iff' i (i + 1) ((i + 1) + 1) (by simp) (by simp)).mpr
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change F.map (K.d (i + 1) ((i + 1) + 1)) x = 0 at hx
    have hx' : (F.map (completionCycleSequence K (i + 1)).g ≫
        F.map (completionCycleSequence K ((i + 1) + 1)).f) x = 0 := by
      rw [← hd]
      exact hx
    have hmi : Function.Injective (F.map (completionCycleSequence K ((i + 1) + 1)).f) :=
      (hs ((i + 1) + 1)).moduleCat_injective_f
    have hxq : F.map (completionCycleSequence K (i + 1)).g x = 0 := by
      apply hmi
      rw [map_zero]
      exact hx' 
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hs (i + 1)).exact x hxq
    obtain ⟨z, hz⟩ := (hs i).moduleCat_surjective_g y
    change F.map (completionCycleSequence K i).g z = y at hz
    change F.map (completionCycleSequence K (i + 1)).f y = x at hy
    refine ⟨z, ?_⟩
    change F.map (K.d i (i + 1)) z = x
    rw [hd]
    change F.map (completionCycleSequence K (i + 1)).f
      (F.map (completionCycleSequence K i).g z) = x
    rw [hz]
    exact hy
  intro j
  simpa only [sub_add_cancel] using hex (j - 1)

/-- 正則な各項を持つ非輪状複体は、各項の H⁰ 主完備化後でも非輪状。 -/
theorem moduleCompletionH0Functor_map_acyclic_of_regular
    (hr : ∀ i, IsSMulRegular (K.X i) a) (hK : K.Acyclic) :
    (((moduleCompletionH0Functor R a).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  apply map_acyclic_of_cycle_sequences K (moduleCompletionH0Functor R a)
  intro i
  exact moduleCompletionH0Functor_shortExact_of_regular a _
    (completionCycleSequence_shortExact K hK i)
    (completionCycle_regular a K hr i) (completionCycle_regular a K hr (i + 1))

/-- 正則な各項を持つ複体の擬同型は、各項の H⁰ 主完備化で擬同型に移る。 -/
theorem moduleCompletionH0Functor_map_quasiIso_of_regular
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hrK : ∀ i, IsSMulRegular (K.X i) a) (hrL : ∀ i, IsSMulRegular (L.X i) a)
    (hf : QuasiIso f) :
    QuasiIso (((moduleCompletionH0Functor R a).mapHomologicalComplex (.up ℤ)).map f) := by
  let C := CochainComplex.mappingCone f
  have hrC (i : ℤ) : IsSMulRegular (C.X i) a := by
    let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl ≪≫
      ModuleCat.biprodIsoProd _ _
    apply (e.toLinearEquiv.isSMulRegular_congr a).mpr
    intro x y h
    exact Prod.ext (hrK (i + 1) (congrArg Prod.fst h)) (hrL i (congrArg Prod.snd h))
  have hC := (cochain_quasiIso_iff_cone_acyclic f).mp hf
  have hFC := moduleCompletionH0Functor_map_acyclic_of_regular a C hrC hC
  apply (cochain_quasiIso_iff_cone_acyclic _).mpr
  exact cochainAcyclic_of_iso hFC
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (moduleCompletionH0Functor R a))

variable {S : Type u} [CommRing S] (φ : R →+* S)

/-- 平坦な係数拡大は、加群上のスカラーの正則性を保つ。 -/
theorem scalarExtension_regular_of_flat (hφ : φ.Flat) (M : ModuleCat.{u} R)
    (hM : IsSMulRegular M a) : IsSMulRegular ((ModuleCat.extendScalars φ).obj M) (φ a) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have hm : Mono (a • 𝟙 M) := (ModuleCat.mono_iff_injective _).mpr hM
  have hmap : Mono ((ModuleCat.extendScalars φ).map (a • 𝟙 M)) := inferInstance
  rw [extendScalars_scalar_id] at hmap
  exact (ModuleCat.mono_iff_injective _).mp hmap

/-- 平坦な係数拡大の後の各項の H⁰ 完備化は、正則な複体の擬同型を保つ。 -/
theorem pointwiseCompletedBaseChangeFunctor_map_quasiIso_of_flat_of_regular
    (hφ : φ.Flat) {K L : CochainComplex (ModuleCat.{u} R) ℤ} (g : K ⟶ L)
    (hrK : ∀ i, IsSMulRegular (K.X i) a) (hrL : ∀ i, IsSMulRegular (L.X i) a)
    (hg : QuasiIso g) :
    QuasiIso (((pointwiseCompletedBaseChangeFunctor a φ).mapHomologicalComplex (.up ℤ)).map g) := by
  let F := ModuleCat.extendScalars φ
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hφ
  have : QuasiIso g := hg
  have hfg : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map g) := inferInstance
  have h := moduleCompletionH0Functor_map_quasiIso_of_regular (φ a)
    ((F.mapHomologicalComplex (.up ℤ)).map g)
    (fun i => scalarExtension_regular_of_flat a φ hφ (K.X i) (hrK i))
    (fun i => scalarExtension_regular_of_flat a φ hφ (L.X i) (hrL i)) hfg
  exact h

/-- 自然数添字の複体の各項の正則性は、整数添字への零延長で保たれる。 -/
theorem cochainNat_extend_regular (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (hr : ∀ i, IsSMulRegular (K.X i) a) (i : ℤ) :
    IsSMulRegular ((K.extend ComplexShape.embeddingUpNat).X i) a := by
  let emb := ComplexShape.embeddingUpNat
  by_cases h : ∃ j, emb.f j = i
  · obtain ⟨j, rfl⟩ := h
    exact ((K.extendXIso emb rfl).toLinearEquiv.isSMulRegular_congr a).mpr (hr j)
  · have hz := K.isZero_extend_X emb i (fun j hj => h ⟨j, hj⟩)
    let : Subsingleton ((K.extend emb).X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    intro x y _
    exact Subsingleton.elim x y

/-- 自然数添字でも、平坦な各項完備係数拡大は正則複体の擬同型を保つ。 -/
theorem pointwiseCompletedBaseChangeNat_quasiIso_of_flat_of_regular
    (hφ : φ.Flat) {K L : CochainComplex (ModuleCat.{u} R) ℕ} (g : K ⟶ L)
    (hrK : ∀ i, IsSMulRegular (K.X i) a) (hrL : ∀ i, IsSMulRegular (L.X i) a)
    (hg : QuasiIso g) :
    QuasiIso (((pointwiseCompletedBaseChangeFunctor a φ).mapHomologicalComplex (.up ℕ)).map g) := by
  let emb := ComplexShape.embeddingUpNat
  let F := pointwiseCompletedBaseChangeFunctor a φ
  have : QuasiIso g := hg
  have hInt := pointwiseCompletedBaseChangeFunctor_map_quasiIso_of_flat_of_regular a φ hφ
    (HomologicalComplex.extendMap g emb)
    (cochainNat_extend_regular a K hrK) (cochainNat_extend_regular a L hrL) inferInstance
  have hc : QuasiIso ((mapExtendIso F K emb).hom ≫
      HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map g) emb) := by
    rw [← mapExtendIso_naturality F emb g]
    infer_instance
  have := hc
  have he : QuasiIso (HomologicalComplex.extendMap
      ((F.mapHomologicalComplex (.up ℕ)).map g) emb) :=
    quasiIso_of_comp_left (mapExtendIso F K emb).hom _
  exact (HomologicalComplex.quasiIso_extendMap_iff _ emb).mp he

end SerrePositivity.DerivedCompletion
