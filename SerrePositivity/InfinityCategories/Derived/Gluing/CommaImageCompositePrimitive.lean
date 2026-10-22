module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaImageCompositionMaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.TensorPrimitiveTransport

/-! 標的恒等 comma への写像は、全 Hom tensor 上の同じ二 primitive とその和を厳密に保存。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : DGFunctorCommaObject R C E F)
local notation "IX" => dgGluingCommaImageObject R C E F X
local notation "IY" => dgGluingCommaImageObject R C E F Y
local notation "IZ" => dgGluingCommaImageObject R C E F Z
local notation "aXY" => dgGluingCommaImageHomMap R C E F X Y
local notation "aYZ" => dgGluingCommaImageHomMap R C E F Y Z

lemma dgGluingCommaImageFirstCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (dgFunctorCommaFirstCompositePrimitive R E E (DGFunctor.id E) IX IY IZ) (zero_add (-1)) =
      dgFunctorCommaFirstCompositePrimitive R C E F X Y Z := by
  have hh : (Cochain.ofHom aXY).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E) IX IY) (zero_add (-1)) =
      (dgFunctorCommaPrimitive R C E F X Y).comp (Cochain.ofHom (𝟙 _)) (add_zero (-1)) := by
    rw [dgGluingCommaImageHomMap_primitive, Cochain.comp_id]
  have ht := dgGluingTensorRightPrimitive_transport (-1) aXY aYZ (𝟙 _) (𝟙 _)
    (dgFunctorCommaPrimitive R C E F X Y)
    (dgFunctorCommaPrimitive R E E (DGFunctor.id E) IX IY)
    (dgFunctorCommaFirstCompositionMap R C E F X Y Z)
    (dgFunctorCommaFirstCompositionMap R E E (DGFunctor.id E) IX IY IZ) hh (by
      rw [Category.comp_id]
      exact dgGluingCommaImageFirstCompositionMap R C E F X Y Z)
  exact ht.trans (Cochain.comp_id _)

lemma dgGluingCommaImageSecondCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (dgFunctorCommaSecondCompositePrimitive R E E (DGFunctor.id E) IX IY IZ) (zero_add (-1)) =
      dgFunctorCommaSecondCompositePrimitive R C E F X Y Z := by
  have hh : (Cochain.ofHom aYZ).comp
      (dgFunctorCommaPrimitive R E E (DGFunctor.id E) IY IZ) (zero_add (-1)) =
      (dgFunctorCommaPrimitive R C E F Y Z).comp (Cochain.ofHom (𝟙 _)) (add_zero (-1)) := by
    rw [dgGluingCommaImageHomMap_primitive, Cochain.comp_id]
  have ht := dgGluingTensorLeftPrimitive_transport (-1) aXY aYZ (𝟙 _) (𝟙 _)
    (dgFunctorCommaPrimitive R C E F Y Z)
    (dgFunctorCommaPrimitive R E E (DGFunctor.id E) IY IZ)
    (dgFunctorCommaSecondCompositionMap R C E F X Y Z)
    (dgFunctorCommaSecondCompositionMap R E E (DGFunctor.id E) IX IY IZ) hh (by
      rw [Category.comp_id]
      exact dgGluingCommaImageSecondCompositionMap R C E F X Y Z)
  exact ht.trans (Cochain.comp_id _)

lemma dgGluingCommaImageCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (dgFunctorCommaCompositePrimitive R E E (DGFunctor.id E) IX IY IZ) (zero_add (-1)) =
      dgFunctorCommaCompositePrimitive R C E F X Y Z := by
  rw [dgFunctorCommaCompositePrimitive, Cochain.comp_add,
    dgGluingCommaImageFirstCompositePrimitive, dgGluingCommaImageSecondCompositePrimitive]
  rfl

end SerrePositivity.InfinityCategories
