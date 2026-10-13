module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.ConeLES
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Regular.SMul

/-! # 加群写像の実導来圏での錐とその零化

加群写像を零次数の cochain 複体の写像へ送り、標準 mapping cone の導来像を取る。
錐上のスカラー作用の零性から、ホモロジー長完全列を使って写像の核と余核の
零化を導く。導来対象やスカラー射を、抽象的な零化条件の代用に置き換えない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- 加群写像を零次数の複体の写像へ送る。 -/
def moduleMapSingle (f : M →ₗ[R] N) :
    (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R M) ⟶
      (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R N) :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map (ModuleCat.ofHom f)

/-- 零次数の加群写像の標準 mapping cone。 -/
def moduleMapConeComplex (f : M →ₗ[R] N) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (moduleMapSingle R f)

/-- 実際の擬同型局所化で構成した導来圏における加群写像の錐。 -/
def moduleMapCone (f : M →ₗ[R] N) : DerivedCompletion.ConcreteDerivedCategory R :=
  DerivedCategory.Q.obj (moduleMapConeComplex R f)

/-- 零次数の加群写像とその錐を結ぶ、実導来圏の標準三角形。 -/
def moduleMapConeTriangle (f : M →ₗ[R] N) :
    Triangle (DerivedCompletion.ConcreteDerivedCategory R) :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (moduleMapSingle R f))

/-- 構成した三角形は実導来圏の完全三角形である。 -/
theorem moduleMapConeTriangle_distinguished (f : M →ₗ[R] N) :
    moduleMapConeTriangle R f ∈ distTriang (DerivedCompletion.ConcreteDerivedCategory R) :=
  DerivedCategory.mappingCone_triangle_distinguished (moduleMapSingle R f)

/-- 標準三角形の第三対象は、構成した加群写像の錐そのものである。 -/
@[simp] theorem moduleMapConeTriangle_obj₃ (f : M →ₗ[R] N) :
    (moduleMapConeTriangle R f).obj₃ = moduleMapCone R f := rfl

/-- 実導来対象である錐上の、R 線形圏の構造によるスカラー自己射。 -/
def moduleMapConeScalar (f : M →ₗ[R] N) (r : R) : moduleMapCone R f ⟶ moduleMapCone R f :=
  r • 𝟙 (moduleMapCone R f)

/-- 導来像のスカラー射が零なら、元の複体の各ホモロジー上の同じ作用も零。 -/
theorem homology_scalar_eq_zero_of_derived_scalar_eq_zero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : R)
    (hK : r • 𝟙 (DerivedCategory.Q.obj K) = 0) (q : ℤ) :
    r • 𝟙 (K.homology q) = 0 := by
  have hQ : DerivedCategory.Q.map (r • 𝟙 K) = 0 := by simpa using hK
  have hn := DerivedCategory.homologyFunctorFactors_hom_naturality
    (r • 𝟙 K) q
  rw [hQ, Functor.map_zero, zero_comp] at hn
  apply (cancel_epi ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q).hom.app K)).mp
  rw [comp_zero]
  simpa only [homologyMap_smul, HomologicalComplex.homologyMap_id] using hn.symm

/-- 実導来錐のスカラー作用が零なら、元の加群写像の核はそのスカラーで消える。 -/
theorem moduleMapConeScalar_eq_zero_annihilates_ker (f : M →ₗ[R] N) (r : R)
    (h : moduleMapConeScalar R f r = 0) : ∀ m : f.ker, r • m = 0 := by
  let eM := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R M))
  let eN := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R N))
  have hnat := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (.up ℤ) 0 (ModuleCat.ofHom f)
  change HomologicalComplex.homologyMap (moduleMapSingle R f) 0 ≫ eN.hom =
    eM.hom ≫ ModuleCat.ofHom f at hnat
  have hH := homology_scalar_eq_zero_of_derived_scalar_eq_zero R
    (moduleMapConeComplex R f) r h (-1)
  intro m
  have hm : HomologicalComplex.homologyMap (moduleMapSingle R f) 0 (eM.inv m) = 0 := by
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    have he : eN.hom (HomologicalComplex.homologyMap (moduleMapSingle R f) 0 (eM.inv m)) =
        f (eM.hom (eM.inv m)) := congrArg (fun a ↦ a (eM.inv m)) hnat
    simpa only [Iso.inv_hom_id_apply, LinearMap.mem_ker.mp m.property, map_zero] using he
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (Cone.exact₁ (moduleMapSingle R f) (-1) 0 (by decide)) (eM.inv m) hm
  have hc0 : r • c = 0 := by
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hH) c
  have hu : r • eM.inv m = 0 := by
    rw [← hc, ← map_smul, hc0, map_zero]
  apply Subtype.ext
  change r • (m : M) = 0
  have he := congrArg eM.hom hu
  simpa only [map_smul, Iso.inv_hom_id_apply, map_zero] using he

/-- 実導来錐のスカラー作用が零なら、元の加群写像の余核はそのスカラーで消える。 -/
theorem moduleMapConeScalar_eq_zero_annihilates_coker (f : M →ₗ[R] N) (r : R)
    (h : moduleMapConeScalar R f r = 0) : ∀ n : N ⧸ f.range, r • n = 0 := by
  let eM := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R M))
  let eN := (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of R N))
  have hnat := HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (.up ℤ) 0 (ModuleCat.ofHom f)
  change HomologicalComplex.homologyMap (moduleMapSingle R f) 0 ≫ eN.hom =
    eM.hom ≫ ModuleCat.ofHom f at hnat
  have hH := homology_scalar_eq_zero_of_derived_scalar_eq_zero R
    (moduleMapConeComplex R f) r h 0
  intro n
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ n
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hn0 : HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (moduleMapSingle R f)) 0 (r • eN.inv n) = 0 := by
    rw [map_smul]
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hH) _
  obtain ⟨m, hm⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (Cone.exact₂ (moduleMapSingle R f) 0) (r • eN.inv n) hn0
  change HomologicalComplex.homologyMap (moduleMapSingle R f) 0 m = r • eN.inv n at hm
  refine ⟨eM.hom m, ?_⟩
  have he : eN.hom (HomologicalComplex.homologyMap (moduleMapSingle R f) 0 m) =
      f (eM.hom m) := congrArg (fun a ↦ a m) hnat
  rw [hm] at he
  simpa only [map_smul, Iso.inv_hom_id_apply] using he.symm

/-- 錐上で g の n 乗が零なら、核と余核の両方を同じ冪が零化する。 -/
theorem moduleMapCone_pow_scalar_eq_zero_annihilates (f : M →ₗ[R] N) (g : R) (n : ℕ)
    (h : (g ^ n) • 𝟙 (moduleMapCone R f) = 0) :
    (∀ m : f.ker, (g ^ n) • m = 0) ∧ (∀ x : N ⧸ f.range, (g ^ n) • x = 0) :=
  ⟨moduleMapConeScalar_eq_zero_annihilates_ker R f (g ^ n) h,
    moduleMapConeScalar_eq_zero_annihilates_coker R f (g ^ n) h⟩

/-- 始域で g が正則なら、実導来錐を g の n 乗で零化する写像は単射で、
同じ冪が余核を零化する。n=0 の場合も含む。 -/
theorem moduleMapCone_pow_scalar_eq_zero_injective_of_regular
    (f : M →ₗ[R] N) (g : R) (n : ℕ) (hg : IsSMulRegular M g)
    (h : (g ^ n) • 𝟙 (moduleMapCone R f) = 0) :
    Function.Injective f ∧ (∀ x : N ⧸ f.range, (g ^ n) • x = 0) := by
  obtain ⟨hker, hcoker⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R f g n h
  refine ⟨?_, hcoker⟩
  intro a b hab
  have hm : a - b ∈ f.ker := by
    rw [LinearMap.mem_ker, map_sub, hab, sub_self]
  have hz : (g ^ n) • (a - b) = 0 := congrArg Subtype.val (hker ⟨a - b, hm⟩)
  exact sub_eq_zero.mp ((hg.pow n) (hz.trans (smul_zero (g ^ n)).symm))

end SerrePositivity
