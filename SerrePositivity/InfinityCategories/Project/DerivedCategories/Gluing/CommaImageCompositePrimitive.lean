module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaImageCompositionMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TensorPrimitiveTransport

/-! 標的恒等 comma への写像は、全 Hom tensor 上の同じ二 primitive とその和を厳密に保存。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F Y
local notation "IZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageObject R C E F Z
local notation "aXY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F X Y
local notation "aYZ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap R C E F Y Z

lemma dgGluingCommaImageFirstCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R E E (DGFunctor.id E) IX IY IZ) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Z := by
  have hh : (Cochain.ofHom aXY).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) IX IY) (zero_add (-1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y).comp (Cochain.ofHom (𝟙 _)) (add_zero (-1)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_primitive, Cochain.comp_id]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTensorRightPrimitive_transport (-1) aXY aYZ (𝟙 _) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) IX IY)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R E E (DGFunctor.id E) IX IY IZ) hh (by
      rw [Category.comp_id]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageFirstCompositionMap R C E F X Y Z)
  exact ht.trans (Cochain.comp_id _)

lemma dgGluingCommaImageSecondCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R E E (DGFunctor.id E) IX IY IZ) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z := by
  have hh : (Cochain.ofHom aYZ).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) IY IZ) (zero_add (-1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z).comp (Cochain.ofHom (𝟙 _)) (add_zero (-1)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageHomMap_primitive, Cochain.comp_id]
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTensorLeftPrimitive_transport (-1) aXY aYZ (𝟙 _) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R E E (DGFunctor.id E) IY IZ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R E E (DGFunctor.id E) IX IY IZ) hh (by
      rw [Category.comp_id]
      exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaImageSecondCompositionMap R C E F X Y Z)
  exact ht.trans (Cochain.comp_id _)

lemma dgGluingCommaImageCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R E E (DGFunctor.id E) IX IY IZ) (zero_add (-1)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F X Y Z := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgGluingCommaImageFirstCompositePrimitive, dgGluingCommaImageSecondCompositePrimitive]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
