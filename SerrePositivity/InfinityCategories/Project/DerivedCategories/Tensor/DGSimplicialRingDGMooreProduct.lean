module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGIntegerCoefficientTensor
/-!
概要：実 Moore 乗法を係数移送後の標準 tensor 成分へ移す。
方針：元の実写像と係数環同型、次数移送を保持して比較する。
規約：単体環の可換性・対象宇宙の縮小を要求しない。使われ方：β5(g)。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
def simplicialRingDGMooreDegreeProduct (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    (E).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X p) ⊗
      (E).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X q) ⟶
        (E).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X (p + q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison _ _ ≫ (E).map
    (HomologicalComplex.ιMapBifunctor _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
      p q (p + q) rfl ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMultiplication A).f (p + q))

lemma simplicialRingDGMooreDegreeProduct_tmul
    (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X p)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X q) :
    (simplicialRingDGMooreDegreeProduct A p q).hom
      (TensorProduct.tmul _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient
        (M := (E).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X p))
        (N := (E).obj ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A).X q)) x y) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDegreeProduct A p q x y := by
  simp only [simplicialRingDGMooreDegreeProduct, ModuleCat.hom_comp, LinearMap.comp_apply,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientTensorComparison_tmul]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
