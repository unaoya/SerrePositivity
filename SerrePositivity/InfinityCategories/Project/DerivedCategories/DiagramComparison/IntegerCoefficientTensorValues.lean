module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZCoefficient
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientFree
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGIntegerCoefficientTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
/-!
概要：係数移送の純テンソル評価を随伴の単位で記す。
方針：指定写像の生成元での値を計算する。規約：A05aの証明分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
/-- 指定係数移送と忘却の随伴の単位。 -/
abbrev coefficientUnit (M : ModuleCat.{u} ℤ) :=
  (simplicialRingIntegerModuleEquivalence.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)).unit.app M
/-- 係数移送したテンソル射の純テンソルの値。 -/
theorem coefficientUnit_tensorMap {M M' N N' : ModuleCat.{u} ℤ}
    (f : M ⟶ M') (g : N ⟶ N') (x : M) (y : N) :
    (integerCoefficientExtension φ).map (integerTensorMap f g)
      (coefficientUnit φ (integerTensor M N) (x ⊗ₜ[ℤ] y)) =
    coefficientUnit φ (integerTensor M' N') (f x ⊗ₜ[ℤ] g y) := by
  rfl
/-- 指定整数テンソル比較とδの純テンソルの値。 -/
theorem coefficientUnit_tensorComparison (M N : ModuleCat.{u} ℤ) (x : M) (y : N) :
    (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ)
      (integerCoefficientModuleFunctor.obj M) (integerCoefficientModuleFunctor.obj N))
      (((ModuleCat.extendScalars φ).map (integerCoefficientTensorIso M N).inv)
        (coefficientUnit φ (integerTensor M N) (x ⊗ₜ[ℤ] y))) =
    TensorProduct.tmul A
      (M := (integerCoefficientExtension φ).obj M)
      (N := (integerCoefficientExtension φ).obj N)
      (coefficientUnit φ M x) (coefficientUnit φ N y) := by
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
