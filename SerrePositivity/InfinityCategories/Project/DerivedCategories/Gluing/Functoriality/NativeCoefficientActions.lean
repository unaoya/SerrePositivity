module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ActionYonedaInverse
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.ComplexPinchedModelInverseNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Coefficients.CoefficientYonedaSpaceIso

/-! 元の二作用の全空間写像を、実 augmentation による加群 Hom の前後合成へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeLeftCoefficientInput (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (yonedaHom R C X.left Y.left) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (representable R X.left) (representable R Y.left)).inv

def dgGluingNativeRightCoefficientInput (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (M.toFunctor.map X.right Y.right) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (M.rightAt X.right) (M.rightAt Y.right)).inv

lemma dgGluingNativeLeftCoefficientAction (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom =
      dgGluingNativeLeftCoefficientInput R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := RightModule R C) (E := RightModule R C)
          (eHomWhiskerLeft (Complex R)
            (ForgetEnrichment.of (Complex R) (representable R X.left))
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedMapIso,
    Iso.trans_hom, Iso.symm_hom, dgGluingNativeLeftCoefficientInput]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftAction_yoneda_inverse R C D M X Y, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedModelInverse_naturality
      (C := RightModule R C) (D := RightModule R C)
      (x := representable R X.left) (y := representable R Y.left)
      (x' := representable R X.left) (y' := M.rightAt Y.right)
      (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M Y))]
  exact (Category.assoc _ _ _).symm

lemma dgGluingNativeRightCoefficientAction (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max (u + 1) v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction R C D M X Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom =
      dgGluingNativeRightCoefficientInput R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := RightModule R C) (E := RightModule R C)
          (eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)
            (ForgetEnrichment.of (Complex R) (M.rightAt Y.right))) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientYonedaSpaceIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedMapIso,
    Iso.trans_hom, Iso.symm_hom, dgGluingNativeRightCoefficientInput]
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightAction_yoneda_inverse R C D M X Y, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedModelInverse_naturality
      (C := RightModule R C) (D := RightModule R C)
      (x := M.rightAt X.right) (y := M.rightAt Y.right)
      (x' := representable R X.left) (y' := M.rightAt Y.right)
      (eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentation R C D M X)
        (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)))]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
