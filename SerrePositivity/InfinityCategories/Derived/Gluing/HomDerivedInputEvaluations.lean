module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedModuleInputFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleFunctorEvaluation
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseNerveComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel

/-! 保存済み二入力の全区間族を、主比較の元の左右 nerve 射影の導来像へ照合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedLeftCoefficientInput_evaluation (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedLeftCoefficientInput R C D M X Y) =
      rightMappingSpacePrism
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
        pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
          dgGluingUniverseLeftNerve R C D M ≫ dgGluingUniverseDerivedYoneda.{u, v, w} R C := by
  refine (dgGluingHomDerivedLeftCoefficientInput_moduleFamily R C D M X Y).trans ?_
  have hF := dgGluingUniverseModuleFunctorEvaluation R C (DGGluingObject R C D M)
    ((dgGluingLeft R C D M).comp (dgYoneda R C)) X Y
  refine hF.trans ?_
  change rightMappingSpacePrism
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
      pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
        dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
          ((dgGluingLeft R C D M).comp (dgYoneda R C)) ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C = _
  have hn := dgGluingUniverseNerveMap_comp.{u, max u v w, v, max (u + 1) v,
    max (u + 1) v w} (dgGluingLeft R C D M) (dgYoneda R C)
  have hh := congrArg (fun k =>
    rightMappingSpacePrism
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
      pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫ k ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) hn
  simpa only [Category.assoc, dgGluingUniversePinchedComplexIso,
    dgGluingUniverseHomMappingIso, dgGluingHomMappingIso, dgGluingUniverseLeftNerve,
    dgGluingUniverseDerivedYoneda,
    dgGluingUniverseYoneda] using hh.symm

lemma dgGluingHomDerivedRightCoefficientInput_evaluation (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedRightCoefficientInput R C D M X Y) =
      rightMappingSpacePrism
          ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
            (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
        pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
          dgGluingUniverseRightNerve R C D M ≫ dgGluingUniverseDerivedCoefficient R C D M := by
  refine (dgGluingHomDerivedRightCoefficientInput_moduleFamily R C D M X Y).trans ?_
  have hF := dgGluingUniverseModuleFunctorEvaluation R C (DGGluingObject R C D M)
    ((dgGluingRight R C D M).comp M.toFunctor) X Y
  refine hF.trans ?_
  change rightMappingSpacePrism
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
      pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫
        dgGluingUniverseNerveMap.{u, max u v w, max (u + 1) v, max (u + 1) v w}
          ((dgGluingRight R C D M).comp M.toFunctor) ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C = _
  have hn := dgGluingUniverseNerveMap_comp.{u, max u v w, w, max (u + 1) v,
    max (u + 1) v w} (dgGluingRight R C D M) M.toFunctor
  have hh := congrArg (fun k =>
    rightMappingSpacePrism
      ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
        (complexPinchedSpace.{u, max u v w} (dgGluingHomComplex R C D M X Y))) ≫
      pinchedHomUncurry (dgGluingUniverseHomMappingIso R C D M X Y).inv ≫ k ≫
        dgGluingUniverseModuleDerivedComparison.{u, v, w} R C) hn
  simpa only [Category.assoc, dgGluingUniversePinchedComplexIso,
    dgGluingUniverseHomMappingIso, dgGluingHomMappingIso, dgGluingUniverseRightNerve,
    dgGluingUniverseDerivedCoefficient,
    dgGluingUniverseCoefficient] using hh.symm

end SerrePositivity.InfinityCategories
