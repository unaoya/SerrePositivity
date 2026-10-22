module
public import SerrePositivity.InfinityCategories.Derived.DGIntegerCoefficientTensor
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
namespace SerrePositivity.InfinityCategories
open scoped TensorProduct
open CategoryTheory MonoidalCategory KST.ProExcision
local notation "E" => integerCoefficientModuleFunctor
def simplicialRingDGMooreDegreeProduct (A : SimplicialObject RingCat.{u}) (p q : ℕ) :
    (E).obj ((simplicialRingNormalizedChains A).X p) ⊗
      (E).obj ((simplicialRingNormalizedChains A).X q) ⟶
        (E).obj ((simplicialRingNormalizedChains A).X (p + q)) :=
  integerCoefficientTensorComparison _ _ ≫ (E).map
    (HomologicalComplex.ιMapBifunctor _ _ integerTensorBifunctor (.down ℕ)
      p q (p + q) rfl ≫ (simplicialRingNormalizedMultiplication A).f (p + q))

lemma simplicialRingDGMooreDegreeProduct_tmul
    (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : (simplicialRingNormalizedChains A).X p)
    (y : (simplicialRingNormalizedChains A).X q) :
    (simplicialRingDGMooreDegreeProduct A p q).hom
      (TensorProduct.tmul simplicialRingCoefficient
        (M := (E).obj ((simplicialRingNormalizedChains A).X p))
        (N := (E).obj ((simplicialRingNormalizedChains A).X q)) x y) =
        simplicialRingNormalizedDegreeProduct A p q x y := by
  simp only [simplicialRingDGMooreDegreeProduct, ModuleCat.hom_comp, LinearMap.comp_apply,
    integerCoefficientTensorComparison_tmul]
  rfl

end SerrePositivity.InfinityCategories
