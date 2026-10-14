module

public import SerrePositivity.HomologicalAlgebra.DerivedModuleCone
public import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-! # 二段の導来対象の零化 -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

private lemma exact_zero_apply {S : ShortComplex (ModuleCat.{u} R)}
    (_ : S.Exact) (x : S.X₁) : S.g (S.f x) = 0 := S.zero_apply x

/-- 完全三角形の両端の零化元の積は中間対象を零化する。 -/
theorem triangle_scalar_product_eq_zero
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (r s : R) (hr : r • 𝟙 T.obj₁ = 0) (hs : s • 𝟙 T.obj₃ = 0) :
    (r * s) • 𝟙 T.obj₂ = 0 := by
  have h : T.mor₁ ≫ (r • 𝟙 T.obj₂) = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp T.mor₁,
      ← Linear.smul_comp, hr, zero_comp]
  obtain ⟨a, ha⟩ := Triangle.yoneda_exact₂ T hT (r • 𝟙 T.obj₂) h
  calc
    (r * s) • 𝟙 T.obj₂ = (r • 𝟙 T.obj₂) ≫ (s • 𝟙 T.obj₂) := by simp [smul_smul, mul_comm]
    _ = (T.mor₂ ≫ a) ≫ (s • 𝟙 T.obj₂) := by rw [ha]
    _ = T.mor₂ ≫ ((s • 𝟙 T.obj₃) ≫ a) := by simp
    _ = 0 := by rw [hs, zero_comp, comp_zero]

/-- 一次数に集中した導来対象の自己射はホモロジー上で検出できる。 -/
theorem scalar_eq_zero_of_single_homology
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) [X.IsGE n] [X.IsLE n]
    (r : R) (hr : r • 𝟙 ((DerivedCategory.homologyFunctor _ n).obj X) = 0) :
    r • 𝟙 X = 0 := by
  obtain ⟨Y, ⟨e⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let d := H.mapIso e
  have hY : r • 𝟙 (H.obj ((DerivedCategory.singleFunctor _ n).obj Y)) = 0 := by
    rw [← cancel_epi d.hom, comp_zero]
    simpa using congrArg (fun z ↦ z ≫ d.hom) hr
  let a := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) n).app Y
  have hY' : r • 𝟙 Y = 0 := by
    rw [← cancel_epi a.hom, comp_zero]
    simpa using congrArg (fun z ↦ z ≫ a.hom) hY
  have hsingle : r • 𝟙 ((DerivedCategory.singleFunctor _ n).obj Y) = 0 := by
    simpa using congrArg (DerivedCategory.singleFunctor _ n).map hY'
  rw [← cancel_mono e.hom, zero_comp]
  simpa using congrArg (fun z ↦ e.hom ≫ z) hsingle

/-- 一次数に集中した複体のホモロジー零化を導来零射へ移す。 -/
theorem derived_scalar_eq_zero_of_single_cohomology
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) [K.IsGE n] [K.IsLE n]
    (r : R) (hr : r • 𝟙 (K.homology n) = 0) :
    r • 𝟙 (DerivedCategory.Q.obj K) = 0 := by
  apply scalar_eq_zero_of_single_homology R _ n r
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      (DerivedCategory.Q.obj K) ≅ K.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app K
  have hh := congrArg (fun z ↦ e.hom ≫ z) hr
  change e.hom ≫ (r • 𝟙 (K.homology n)) = 0 at hh
  rw [Linear.comp_smul, Category.comp_id] at hh
  rw [← cancel_mono e.hom, zero_comp, Linear.smul_comp, Category.id_comp]
  exact hh

/-- 二つの隣接次数だけに項を持つ複体では、両ホモロジーの零化元の積が導来対象を消す。 -/
theorem two_term_derived_scalar_product_eq_zero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hab : a + 1 = b)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] (r s : R)
    (hr : r • 𝟙 (K.homology a) = 0) (hs : s • 𝟙 (K.homology b) = 0) :
    (r * s) • 𝟙 (DerivedCategory.Q.obj K) = 0 := by
  have hleft : r • 𝟙 (DerivedCategory.Q.obj (K.truncLE a)) = 0 := by
    apply derived_scalar_eq_zero_of_single_cohomology R _ a r
    let e := asIso (HomologicalComplex.homologyMap (K.ιTruncLE a) a)
    rw [← cancel_mono e.hom, zero_comp]
    simpa only [Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp, comp_zero] using
      congrArg (fun z ↦ e.hom ≫ z) hr
  have hright : s • 𝟙 (DerivedCategory.Q.obj (K.truncGE b)) = 0 := by
    apply derived_scalar_eq_zero_of_single_cohomology R _ b s
    let e := asIso (HomologicalComplex.homologyMap (K.πTruncGE b) b)
    rw [← cancel_epi e.hom, comp_zero]
    simpa using congrArg (fun z ↦ z ≫ e.hom) hs
  let h := K.shortComplexTruncLE_shortExact a
  let e := asIso (DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE a b hab))
  have hright' : s • 𝟙 (DerivedCategory.Q.obj (K.shortComplexTruncLE a).X₃) = 0 := by
    rw [← cancel_mono e.hom, zero_comp]
    simpa only [Linear.comp_smul, Linear.smul_comp, Category.comp_id,
      Category.id_comp, comp_zero] using
      congrArg (fun z ↦ e.hom ≫ z) hright
  exact triangle_scalar_product_eq_zero R (DerivedCategory.triangleOfSES h)
    (DerivedCategory.triangleOfSES_distinguished h) r s hleft hright'

variable {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- 加群写像の錐の項は-1次以上にある。 -/
instance moduleMapConeComplex_isStrictlyGE (f : M →ₗ[R] N) :
    (moduleMapConeComplex R f).IsStrictlyGE (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).mpr
  constructor <;> exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- 加群写像の錐の項は0次以下にある。 -/
instance moduleMapConeComplex_isStrictlyLE (f : M →ₗ[R] N) :
    (moduleMapConeComplex R f).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).mpr
  constructor <;> exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

/-- 核の零化は錐の-1次ホモロジーを零化する。 -/
theorem moduleMapCone_homology_neg_one_scalar_eq_zero
    (f : M →ₗ[R] N) (r : R) (hr : ∀ x : M, f x = 0 → r • x = 0) :
    r • 𝟙 ((moduleMapConeComplex R f).homology (-1)) = 0 := by
  let φ := moduleMapSingle R f
  let eM := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R M)
  let eN := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R N)
  have hnat := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (.up ℤ) 0 (ModuleCat.ofHom f)
  change HomologicalComplex.homologyMap φ 0 ≫ eN.hom = eM.hom ≫ ModuleCat.ofHom f at hnat
  change r • 𝟙 ((Cone.cone φ).homology (-1)) = 0
  ext z
  change r • z = 0
  have hzker : f (eM.hom (Cone.δ φ (-1) 0 (by decide) z)) = 0 := by
    have heq := congrArg (fun t ↦ t (Cone.δ φ (-1) 0 (by decide) z)) hnat
    change eN.hom (HomologicalComplex.homologyMap φ 0
      (Cone.δ φ (-1) 0 (by decide) z)) =
        f (eM.hom (Cone.δ φ (-1) 0 (by decide) z)) at heq
    rw [← heq]
    have hh := exact_zero_apply R (Cone.exact₁ φ (-1) 0 (by decide)) z
    simpa using congrArg eN.hom hh
  have hδ : Cone.δ φ (-1) 0 (by decide) (r • z) = 0 := by
    apply (ModuleCat.mono_iff_injective eM.hom).mp inferInstance
    simpa using hr _ hzker
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (Cone.exact₃ φ (-1) 0 (by decide)) (r • z) hδ
  have hwzero : w = 0 := by
    have hzero := HomologicalComplex.exactAt_single_obj (.up ℤ) 0
      (ModuleCat.of R N) (-1) (by decide)
    exact ModuleCat.isZero_iff_subsingleton.mp hzero.isZero_homology |>.elim _ _
  simpa [hwzero] using hw.symm

/-- 余核の零化は錐の0次ホモロジーを零化する。 -/
theorem moduleMapCone_homology_zero_scalar_eq_zero
    (f : M →ₗ[R] N) (s : R) (hs : ∀ y : N ⧸ f.range, s • y = 0) :
    s • 𝟙 ((moduleMapConeComplex R f).homology 0) = 0 := by
  let φ := moduleMapSingle R f
  let eM := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R M)
  let eN := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R N)
  have hnat := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (.up ℤ) 0 (ModuleCat.ofHom f)
  change HomologicalComplex.homologyMap φ 0 ≫ eN.hom = eM.hom ≫ ModuleCat.ofHom f at hnat
  change s • 𝟙 ((Cone.cone φ).homology 0) = 0
  ext z
  change s • z = 0
  have hδ : Cone.δ φ 0 1 (by decide) z = 0 := by
    have hzero := HomologicalComplex.exactAt_single_obj (.up ℤ) 0
      (ModuleCat.of R M) 1 (by decide)
    exact ModuleCat.isZero_iff_subsingleton.mp hzero.isZero_homology |>.elim _ _
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (Cone.exact₃ φ 0 1 (by decide)) z hδ
  have hmem : s • eN.hom w ∈ f.range := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact (map_smul f.range.mkQ s (eN.hom w)).trans (hs _)
  obtain ⟨m, hm⟩ := hmem
  have hmap : HomologicalComplex.homologyMap φ 0 (eM.inv m) = s • w := by
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    have heq := congrArg (fun t ↦ t (eM.inv m)) hnat
    change eN.hom (HomologicalComplex.homologyMap φ 0 (eM.inv m)) =
      f (eM.hom (eM.inv m)) at heq
    simpa only [Iso.inv_hom_id_apply, map_smul, hm] using heq
  have hz := exact_zero_apply R (Cone.exact₂ φ 0) (eM.inv m)
  change HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) 0
    (HomologicalComplex.homologyMap φ 0 (eM.inv m)) = 0 at hz
  rw [hmap, map_smul, hw] at hz
  exact hz

/-- 任意の加群写像について、核と余核の零化元の積が実導来錐上の零射となる。 -/
theorem moduleMapConeScalar_eq_zero_of_ker_coker_annihilated
    (f : M →ₗ[R] N) (r s : R)
    (hr : ∀ x : M, f x = 0 → r • x = 0)
    (hs : ∀ y : N ⧸ f.range, s • y = 0) :
    moduleMapConeScalar R f (r * s) = 0 :=
  two_term_derived_scalar_product_eq_zero R (moduleMapConeComplex R f) (-1) 0
    (by decide) r s (moduleMapCone_homology_neg_one_scalar_eq_zero R f r hr)
    (moduleMapCone_homology_zero_scalar_eq_zero R f s hs)

end SerrePositivity
