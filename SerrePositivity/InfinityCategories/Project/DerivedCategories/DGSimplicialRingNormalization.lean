module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedShuffle
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Algebra.Bilinear
/-!
概要：単体環の実正規化乗法と、元の shuffle の経路・符号の整合性。
方針：既存の実 shuffle 鎖写像と同じ有限和の座標・係数を使う。
規約：元の非可換な積と全次数を保つ。使われ方：β5(g) の dg 代数化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology AlgebraicTopology.DoldKan
open scoped _root_.Simplicial

def ringIntegerModuleFunctor : RingCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toAddMonoidHom.toIntLinearMap
  map_id A := by ext x; rfl
  map_comp f g := by ext x; rfl
abbrev simplicialRingIntegerModule (A : SimplicialObject RingCat.{u}) :=
  A ⋙ ringIntegerModuleFunctor
abbrev simplicialRingIntegerModuleMap {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :=
  Functor.whiskerRight f ringIntegerModuleFunctor

def simplicialRingIntegerMultiplication (A : SimplicialObject RingCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A where
  app n := ModuleCat.ofHom (LinearMap.mul' ℤ (A.obj n))
  naturality n m φ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    exact ((A.map φ).hom.map_mul x y).symm
lemma simplicialRingIntegerMultiplication_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModuleMap f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModuleMap f) ≫ simplicialRingIntegerMultiplication B =
      simplicialRingIntegerMultiplication A ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModuleMap f := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  exact ((f.app n).hom.map_mul x y).symm
abbrev simplicialRingNormalizedChains (A : SimplicialObject RingCat.{u}) :=
  (normalizedMooreComplex _).obj (simplicialRingIntegerModule A)
abbrev simplicialRingNormalizedMap {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :=
  (normalizedMooreComplex _).map (simplicialRingIntegerModuleMap f)
def simplicialRingNormalizedMultiplication (A : SimplicialObject RingCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingIntegerModule A) ≫
    (normalizedMooreComplex _).map (simplicialRingIntegerMultiplication A)
lemma simplicialRingNormalizedMultiplication_naturality
    {A B : SimplicialObject RingCat.{u}} (f : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f) ≫
        simplicialRingNormalizedMultiplication B =
      simplicialRingNormalizedMultiplication A ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap f := by
  dsimp only [simplicialRingNormalizedMultiplication, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedMap]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalizedShuffle_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [simplicialRingIntegerMultiplication_naturality]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
