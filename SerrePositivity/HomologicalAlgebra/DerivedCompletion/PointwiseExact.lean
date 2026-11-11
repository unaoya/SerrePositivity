module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseRegular
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# 正則な両端を持つ短完全列の各項完備化

## 概要
指定スカラーが両端の加群上で正則な短完全列は、H⁰ 主完備化の後でも短完全。

## 方針
短完全列の標準導来三角形を完備化し、両端の完備化の純性とホモロジー長完全列を使う。

## 規約
中央の加群の正則性や基底の平坦性は追加仮定にしない。

## 使われ方
BS 著者版 Theorem 6.4 の正則な各項を持つ古典的な複体の完備係数変更。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace SerrePositivity.DerivedCompletion

attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (a : R)

/-- スカラーが両端で正則な短完全列の H⁰ 主完備化は短完全。 -/
theorem moduleCompletionH0Functor_shortExact_of_regular
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsSMulRegular S.X₁ a) (h₃ : IsSMulRegular S.X₃ a) :
    (S.map (moduleCompletionH0Functor R a)).ShortExact := by
  let F := derivedComplexCompletionFunctor R a
  let T₀ := DerivedCategory.triangleOfSES
    (hS.map_of_exact (CochainComplex.singleFunctor (ModuleCat R) 0))
  let T := F.mapTriangle.obj T₀
  have hd : T ∈ distTriang _ := F.map_distinguished _
    (DerivedCategory.triangleOfSES_distinguished
      (hS.map_of_exact (CochainComplex.singleFunctor (ModuleCat R) 0)))
  have h₁' := moduleCompletionH0_regular_pure a S.X₁ h₁
  have h₃' := moduleCompletionH0_regular_pure a S.X₃ h₃
  let : T.obj₁.IsLE 0 := h₁'.2.1
  let : T.obj₃.IsGE 0 := h₃'.1
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) 1).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE _ 0 1 (by omega)
  have hz₃ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE _ 0 (-1) (by omega)
  let S' := S.map (moduleCompletionH0Functor R a)
  have hm : Mono S'.f := by
    change Mono ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map T.mor₁)
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hd (-1) 0
      (by omega)).mpr
    exact hz₃.eq_zero_of_src _
  have he : Epi S'.g := by
    change Epi ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map T.mor₂)
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hd 0 1
      (by omega)).mpr
    exact hz₁.eq_zero_of_tgt _
  refine ⟨?_⟩
  exact DerivedCategory.HomologySequence.exact₂ T hd 0

end SerrePositivity.DerivedCompletion
