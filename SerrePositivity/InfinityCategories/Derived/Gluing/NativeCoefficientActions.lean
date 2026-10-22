module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ActionYonedaInverse
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedModelInverseNaturality
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientYonedaSpaceIso

/-! 元の二作用の全空間写像を、実 augmentation による加群 Hom の前後合成へ同定する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingNativeLeftCoefficientInput (X Y : DGGluingObject R C D M) :=
  complexPinchedMap.{u, max (u + 1) v} (yonedaHom R C X.left Y.left) ≫
    (pinchedComplexModelIso (representable R X.left) (representable R Y.left)).inv

def dgGluingNativeRightCoefficientInput (X Y : DGGluingObject R C D M) :=
  complexPinchedMap.{u, max (u + 1) v} (M.toFunctor.map X.right Y.right) ≫
    (pinchedComplexModelIso (M.rightAt X.right) (M.rightAt Y.right)).inv

lemma dgGluingNativeLeftCoefficientAction (X Y : DGGluingObject R C D M) :
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
        (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom =
      dgGluingNativeLeftCoefficientInput R C D M X Y ≫
        pinchedHomChainMap (D := RightModule R C) (E := RightModule R C)
          (eHomWhiskerLeft (Complex R)
            (ForgetEnrichment.of (Complex R) (representable R X.left))
            (dgGluingAugmentation R C D M Y)) := by
  dsimp only [dgGluingCoefficientYonedaSpaceIso, dgGluingComplexPinchedMapIso,
    Iso.trans_hom, Iso.symm_hom, dgGluingNativeLeftCoefficientInput]
  rw [← Category.assoc, ← complexPinchedMap_comp,
    dgGluingLeftAction_yoneda_inverse R C D M X Y, complexPinchedMap_comp, Category.assoc,
    dgGluingComplexPinchedModelInverse_naturality
      (C := RightModule R C) (D := RightModule R C)
      (x := representable R X.left) (y := representable R Y.left)
      (x' := representable R X.left) (y' := M.rightAt Y.right)
      (eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (representable R X.left))
        (dgGluingAugmentation R C D M Y))]
  exact (Category.assoc _ _ _).symm

lemma dgGluingNativeRightCoefficientAction (X Y : DGGluingObject R C D M) :
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
        (dgGluingCoefficientYonedaSpaceIso R C X.left (M.rightAt Y.right)).hom =
      dgGluingNativeRightCoefficientInput R C D M X Y ≫
        pinchedHomChainMap (D := RightModule R C) (E := RightModule R C)
          (eHomWhiskerRight (Complex R) (dgGluingAugmentation R C D M X)
            (ForgetEnrichment.of (Complex R) (M.rightAt Y.right))) := by
  dsimp only [dgGluingCoefficientYonedaSpaceIso, dgGluingComplexPinchedMapIso,
    Iso.trans_hom, Iso.symm_hom, dgGluingNativeRightCoefficientInput]
  rw [← Category.assoc, ← complexPinchedMap_comp,
    dgGluingRightAction_yoneda_inverse R C D M X Y, complexPinchedMap_comp, Category.assoc,
    dgGluingComplexPinchedModelInverse_naturality
      (C := RightModule R C) (D := RightModule R C)
      (x := M.rightAt X.right) (y := M.rightAt Y.right)
      (x' := representable R X.left) (y' := M.rightAt Y.right)
      (eHomWhiskerRight (Complex R) (dgGluingAugmentation R C D M X)
        (ForgetEnrichment.of (Complex R) (M.rightAt Y.right)))]
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories
