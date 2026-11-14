module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeModuleCochainInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.UniverseTransport.UniverseSimplexFamilies

/-! 実 native 正規化 Hom に元 augmentation を適用した全 pinched prism は、同じ明示 cochain 族。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "RM" => _root_.SerrePositivity.DifferentialGraded.RightModule R C
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R C) (RightModule R C)
  (_root_.SerrePositivity.DifferentialGraded.DGFunctor.id (_root_.SerrePositivity.DifferentialGraded.RightModule R C))
local notation "q" => CategoryTheory.Iso.inv (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R X.left (M.rightAt Y.right))
local notation "f" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y
local notation "g" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y
local notation "h" => -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomPrimitive R C D M X Y

def dgGluingNativeModuleNormalizedPrism :=
  (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseHomChainMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
    (C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (D := Q) (x := X) (y := Y)
    (x' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (representable R X.left))
    (y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R RM (M.rightAt Y.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom R C D M X Y)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism R RM (representable R X.left) (M.rightAt Y.right))

lemma dgGluingNativeModuleNormalizedPrism_cochain :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainModelInput R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainPrism R C D M X Y) =
      dgGluingNativeModuleNormalizedPrism R C D M X Y := by
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily_precomp.{max (u + 1) v, max (u + 1) v w}
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism R RM (representable R X.left) (M.rightAt Y.right))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainIdentityCommaPinchedInput.{u, max (u + 1) v}
      R RM (_root_.SerrePositivity.DifferentialGraded.representable R X.left) (M.rightAt Y.right)
      K (f ≫ q) (g ≫ q) (Cochain.comp h (Cochain.ofHom q) (add_zero (-1)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedCochain_boundary R C D M X Y))
  change _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{max (u + 1) v, max (u + 1) v w} 1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainPrism R C D M X Y) at hu
  rw [← hu, ← Category.assoc, ← whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeModuleCochainInput_factor]
  rw [dgGluingNativeModuleNormalizedPrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeNormalizedHom_eq_cochainLift]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
