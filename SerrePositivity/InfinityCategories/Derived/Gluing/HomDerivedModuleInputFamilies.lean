module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleFamilyPrecomp

/-! 保存済みの導来二入力を、元の加群値合成 dg 関手の全 Hom 作用として読む。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingHomDerivedLeftCoefficientInput_moduleFamily (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedLeftCoefficientInput R C D M X Y) =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v}
          (((dgGluingLeft R C D M).comp (dgYoneda R C)).map X Y) ≫
          (pinchedComplexModelIso (representable R X.left) (representable R Y.left)).inv)) := by
  rw [dgGluingHomDerivedLeftCoefficientInput_uncurry R C D M X Y,
    dgGluingUniverseModuleDerivedFamilyInterval_precomp R C,
    dgGluingNativeLeftCoefficientInput]
  apply congrArg intervalMappingUncurry
  apply congrArg (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C)
  rw [← Category.assoc, ← complexPinchedMap_comp]
  rfl

lemma dgGluingHomDerivedRightCoefficientInput_moduleFamily (X Y : DGGluingObject R C D M) :
    intervalMappingUncurry (dgGluingHomDerivedRightCoefficientInput R C D M X Y) =
      intervalMappingUncurry (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v}
          (((dgGluingRight R C D M).comp M.toFunctor).map X Y) ≫
          (pinchedComplexModelIso (M.rightAt X.right) (M.rightAt Y.right)).inv)) := by
  have hm : ((dgGluingRight R C D M).comp M.toFunctor).map X Y =
      dgGluingRightHomMap R C D M X Y ≫ M.toFunctor.map X.right Y.right := by
    change (dgGluingRight R C D M).map X Y ≫ M.toFunctor.map X.right Y.right = _
    exact congrArg (fun k => k ≫ M.toFunctor.map X.right Y.right)
      (dgGluingRight_map R C D M X Y)
  rw [dgGluingHomDerivedRightCoefficientInput_uncurry R C D M X Y,
    dgGluingUniverseModuleDerivedFamilyInterval_precomp R C,
    dgGluingNativeRightCoefficientInput]
  apply congrArg intervalMappingUncurry
  apply congrArg (dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C)
  rw [← Category.assoc, ← complexPinchedMap_comp]
  exact congrArg (fun k => complexPinchedMap.{u, max (u + 1) v} k ≫
    (pinchedComplexModelIso (M.rightAt X.right) (M.rightAt Y.right)).inv) hm.symm

end SerrePositivity.InfinityCategories
