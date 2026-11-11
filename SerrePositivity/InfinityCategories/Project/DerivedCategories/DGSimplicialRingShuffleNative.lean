module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingShuffleProduct
/-!
概要：単体環の実 shuffle 積を、元の shuffle 鎖写像の二重次数成分へ同定する。
方針：同じ経路・符号と純テンソルの評価を照合する。
規約：実整数 tensor と元の環の積を保持。使われ方：正規化乗法の結合・単位への接続。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite
open scoped _root_.Simplicial
universe u
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma simplicialRingShuffleProduct_eq_shuffleBidegree
    (A : SimplicialObject RingCat.{u}) (p q : ℕ)
    (x : A.obj (op ⦋p⦌)) (y : A.obj (op ⦋q⦌)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A)
      p q (p + q) rfl ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerMultiplication A).app (op ⦋p + q⦌)).hom
        (TensorProduct.tmul ℤ x y) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingShuffleProduct A p q x y := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.shuffleBidegree, Preadditive.sum_comp]
  simp only [Functor.comp_obj, Int.reduceNeg, Functor.comp_map, Linear.smul_comp,
    ModuleCat.hom_sum, ModuleCat.hom_smul, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
    LinearMap.restrictScalars_self, LinearMap.coe_sum, LinearMap.coe_smul, LinearMap.coe_comp,
    Finset.sum_apply, Pi.smul_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro s _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.sign_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.left_eq_horizontal,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.NormalizedRingShuffle.right_eq_vertical]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
