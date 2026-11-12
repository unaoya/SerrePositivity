module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeCoefficientActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedPrecompositionAW
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedFamilyComposition

/-! 元の augmentation と二入力の実 AW 合成族は、元の二作用そのものである。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingNativeLeftCoefficientComposition (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y)
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomCompositionFamily_closed_post]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientAction R C D M X Y).symm

lemma dgGluingNativeRightCoefficientComposition (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositionFamily_closed_pre]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientAction R C D M X Y).symm

lemma dgGluingNativeLeftCoefficientFamily_comp (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom R (RightModule R C) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeLeftCoefficientInput R C D M X Y) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom R (RightModule R C)
          (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y))) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom R (RightModule R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp, dgGluingNativeLeftCoefficientComposition R C D M X Y]

lemma dgGluingNativeRightCoefficientFamily_comp (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom R (RightModule R C)
        (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R (RightModule R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom R (RightModule R C)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeRightCoefficientInput R C D M X Y) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom R (RightModule R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom_comp, dgGluingNativeRightCoefficientComposition R C D M X Y]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
