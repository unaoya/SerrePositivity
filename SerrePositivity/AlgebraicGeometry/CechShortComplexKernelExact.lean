module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
概要：短完全列間のepiの同じ核へ、既存のsnake lemmaを適用する。
方針：既存の核・余核をSnakeInputへ代入し、同じ中項の核も比較する。
規約：選んだ核とその包含を保持する。
使われ方：実際のF8と基底列の比較から元の核の短完全列を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category* C] [Abelian C] {S T : ShortComplex C}
variable (φ : S ⟶ T)

private def cechKernelSnakeInput (hS : S.ShortExact) (hT : T.ShortExact) :
    ShortComplex.SnakeInput C where
  L₀ := kernel φ
  L₁ := S
  L₂ := T
  L₃ := cokernel φ
  v₀₁ := kernel.ι φ
  v₁₂ := φ
  v₂₃ := cokernel.π φ
  w₀₂ := kernel.condition φ
  w₁₃ := cokernel.condition φ
  h₀ := kernelIsKernel φ
  h₃ := cokernelIsCokernel φ
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

/-- 既存snake lemmaにより、短完全列間のepiの同じ核は短完全。 -/
theorem cechShortComplexKernel_shortExact [Epi φ]
    (hS : S.ShortExact) (hT : T.ShortExact) : (kernel φ).ShortExact := by
  let D := cechKernelSnakeInput φ hS hT
  haveI : Mono D.L₁.f := hS.mono_f
  have hm : Mono D.L₀.f := inferInstance
  have hz : IsZero D.L₃.X₁ :=
    (ShortComplex.π₁ : ShortComplex C ⥤ C).map_isZero (isZero_cokernel_of_epi φ)
  have he : Epi D.L₀.g := D.L₁'_exact.epi_f_iff.mpr (hz.eq_zero_of_tgt _)
  exact { exact := D.L₀_exact, mono_f := hm, epi_g := he }

set_option backward.isDefEq.respectTransparency false in
/-- 既存のπ₁の核保存による、元の左項の核との標準比較。 -/
def cechShortComplexKernelLeftIso : (kernel φ).X₁ ≅ kernel φ.τ₁ :=
  PreservesKernel.iso (ShortComplex.π₁ : ShortComplex C ⥤ C) φ

set_option backward.isDefEq.respectTransparency false in
/-- 既存のπ₃の核保存による、元の右項の核との標準比較。 -/
def cechShortComplexKernelRightIso : (kernel φ).X₃ ≅ kernel φ.τ₃ :=
  PreservesKernel.iso (ShortComplex.π₃ : ShortComplex C ⥤ C) φ

set_option backward.isDefEq.respectTransparency false in
/-- 既存のπ₂の核保存により、同じ短複体の中項と元の中項の核を比較する。 -/
def cechShortComplexKernelMiddleIso : (kernel φ).X₂ ≅ kernel φ.τ₂ :=
  PreservesKernel.iso (ShortComplex.π₂ : ShortComplex C ⥤ C) φ

set_option backward.isDefEq.respectTransparency false in
/-- 同じ中項の標準比較は、元の核の包含を保つ。 -/
theorem cechShortComplexKernelMiddleIso_hom_ι :
    (cechShortComplexKernelMiddleIso φ).hom ≫ kernel.ι φ.τ₂ = (kernel.ι φ).τ₂ := by
  exact (congrArg (fun z ↦ z ≫ kernel.ι φ.τ₂)
    (PreservesKernel.iso_hom (ShortComplex.π₂ : ShortComplex C ⥤ C) φ)).trans
      (kernelComparison_comp_ι φ (ShortComplex.π₂ : ShortComplex C ⥤ C))

end SerrePositivity.AlgebraicGeometry
