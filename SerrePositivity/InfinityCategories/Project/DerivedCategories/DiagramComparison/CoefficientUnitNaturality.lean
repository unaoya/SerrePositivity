module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorValues

/-!
概要：指定係数移送の単位は元の整数加群射に自然で、その像がA線形射を検出する。
方針：同じ係数拡大随伴の単位の定義とHom同値の単射性を使う。
規約：元の係数環・全加群・全射を保持する既存構成の単位・自然性則。
使われ方：HA 1.2.4、IS-W2 B02のraw AW成分の係数移送後の等式。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open scoped TensorProduct
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 同じ係数移送の単位の元の射による像。 -/
theorem coefficientUnit_map_value {M N : ModuleCat.{u} ℤ} (f : M ⟶ N) (x : M) :
    (integerCoefficientExtension φ).map f (coefficientUnit φ M x) =
      coefficientUnit φ N (f x) := by
  rfl

/-- 指定単位の全ての元の像の一致は、元の係数移送後のA線形射を検出する。 -/
theorem coefficientUnit_hom_ext (M : ModuleCat.{u} ℤ) (N : ModuleCat.{u} A)
    (f g : (integerCoefficientExtension φ).obj M ⟶ N)
    (h : ∀ x : M, f (coefficientUnit φ M x) = g (coefficientUnit φ M x)) : f = g := by
  let adj := simplicialRingIntegerModuleEquivalence.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)
  apply (adj.homEquiv M N).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact h x

/-- 同じ係数単位の二つの整数自由生成元の値だけで、移送後のtensorからの射を検出する。 -/
theorem coefficientUnit_integerTensor_hom_ext (X Y : Type u) (N : ModuleCat.{u} A)
    (f g : (integerCoefficientExtension φ).obj
      (integerTensor (integerLinearization.obj X) (integerLinearization.obj Y)) ⟶ N)
    (h : ∀ x y, f (coefficientUnit φ _ (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
      g (coefficientUnit φ _ (integerGenerator x ⊗ₜ[ℤ] integerGenerator y))) : f = g := by
  let adj := simplicialRingIntegerModuleEquivalence.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj φ)
  apply (adj.homEquiv _ N).injective
  apply integerTensor_hom_ext
  intro x y
  exact h x y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
