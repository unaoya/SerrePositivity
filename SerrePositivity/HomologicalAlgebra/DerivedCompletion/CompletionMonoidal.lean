module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBraided
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAlgebraAugmentation
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import Mathlib.Algebra.Algebra.Bilinear
public import SerrePositivity.HomologicalAlgebra.DerivedDiscretePointAction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection

/-! # 完備化のテンソル積と導来代数

## 概要

完備化の同値がテンソル積で安定であることと、標準のテンソル比較（`boundedAboveCompletionTensorComparison`）の結合・対称・単位の両立を示し、可換な導来代数の対象の完備化（`boundedAboveCompletionCommMonFunctor`）、H⁰ の代数の図式、非正の源の上の H⁰ の代数としての普遍性（`completionH0AlgebraLift`）、代数の点の乗法の保存を与える。

## 方針

Mathlib の `Functor.mapCommMon` を使う。

## 規約

旧 `CompletionTensorComparison`・`CompletionTensorCoherence`・`CompletionAlgebraObjects`・`CompletionH0Algebra`・`CompletionH0AlgebraUniversal`・`CompletionPointAction`。

## 使われ方

`CompletedTensorVanishing` 以降、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section CompletionTensorComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Tensoring on the right preserves actual completion equivalences. -/
theorem completionEquivalence_whiskerRight {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) (Z : D) :
    IsIso ((derivedComplexCompletionFunctor R a).map (f ▷ Z).hom) := by
  apply boundedAboveCompletion_map_isIso_of_koszul R a
  intro n
  apply (boundedAboveDerivedTensorKoszul_isIso_iff (a ^ n) (f ▷ Z)).mp
  have : IsIso (boundedAboveKoszulObject (a ^ n) ◁ f) :=
    (boundedAboveDerivedTensorKoszul_isIso_iff (a ^ n) f).mpr
      (derivedScalarCone_map_isIso_of_completion R a f.hom hf n)
  rw [whisker_assoc_symm]
  infer_instance

/-- Tensoring on the left preserves actual completion equivalences. -/
theorem completionEquivalence_whiskerLeft {X Y : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) (Z : D) :
    IsIso ((derivedComplexCompletionFunctor R a).map (Z ◁ f).hom) := by
  have := completionEquivalence_whiskerRight R a f hf Z
  have he : Z ◁ f = (β_ Z X).hom ≫ (f ▷ Z) ≫ (β_ Z Y).inv := by
    apply (cancel_mono (β_ Z Y).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact BraidedCategory.braiding_naturality_right Z f
  rw [he, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Tensoring two completion equivalences again gives a completion equivalence. -/
theorem completionEquivalence_tensorHom {X Y U V : D} (f : X ⟶ Y) (g : U ⟶ V)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom))
    (hg : IsIso ((derivedComplexCompletionFunctor R a).map g.hom)) :
    IsIso ((derivedComplexCompletionFunctor R a).map (f ⊗ₘ g).hom) := by
  have := completionEquivalence_whiskerRight R a f hf U
  have := completionEquivalence_whiskerLeft R a g hg Y
  rw [tensorHom_def, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
  infer_instance

/-- Completion inverts the tensor product of its two actual standard units. -/
theorem boundedAboveCompletion_tensor_unit_isIso (X Y : D) :
    IsIso ((boundedAboveDerivedCompletionFunctor R a).map
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y)) := by
  have h := completionEquivalence_tensorHom R a
    ((boundedAboveDerivedCompletionUnit R a).app X)
    ((boundedAboveDerivedCompletionUnit R a).app Y)
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
    (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj)
  have : IsIso (DerivedCategory.Minus.ι.map ((boundedAboveDerivedCompletionFunctor R a).map
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y))) := h
  exact isIso_of_reflects_iso _ DerivedCategory.Minus.ι

/-- The canonical lax tensor comparison, built from the original standard unit. -/
def boundedAboveCompletionTensorComparison (X Y : D) :
    (boundedAboveDerivedCompletionFunctor R a).obj X ⊗
        (boundedAboveDerivedCompletionFunctor R a).obj Y ⟶
      (boundedAboveDerivedCompletionFunctor R a).obj (X ⊗ Y) := by
  have := boundedAboveCompletion_tensor_unit_isIso R a X Y
  exact (boundedAboveDerivedCompletionUnit R a).app _ ≫
    inv ((boundedAboveDerivedCompletionFunctor R a).map
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y))

/-- The comparison extends the original tensor product of standard units. -/
theorem boundedAboveCompletionTensorComparison_unit (X Y : D) :
    ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
      (boundedAboveDerivedCompletionUnit R a).app Y) ≫
        boundedAboveCompletionTensorComparison R a X Y =
      (boundedAboveDerivedCompletionUnit R a).app (X ⊗ Y) := by
  have := boundedAboveCompletion_tensor_unit_isIso R a X Y
  let t := (boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
    (boundedAboveDerivedCompletionUnit R a).app Y
  have ht := (boundedAboveDerivedCompletionUnit R a).naturality t
  change t ≫ (boundedAboveDerivedCompletionUnit R a).app _ =
    (boundedAboveDerivedCompletionUnit R a).app _ ≫
      (boundedAboveDerivedCompletionFunctor R a).map t at ht
  change t ≫ ((boundedAboveDerivedCompletionUnit R a).app _ ≫
    inv ((boundedAboveDerivedCompletionFunctor R a).map t)) = _
  rw [← Category.assoc, ht, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- Maps to a complete target are determined along any completion equivalence. -/
theorem completionEquivalence_hom_ext
    {X Y Z : ConcreteDerivedCategory R} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f))
    (hZ : IsComplete R a Z) {g h : Y ⟶ Z} (he : f ≫ g = f ≫ h) : g = h := by
  have := hf
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a Z hZ
  have hm : (derivedComplexCompletionFunctor R a).map g =
      (derivedComplexCompletionFunctor R a).map h := by
    apply (cancel_epi ((derivedComplexCompletionFunctor R a).map f)).mp
    simpa only [← Functor.map_comp] using
      congrArg (derivedComplexCompletionFunctor R a).map he
  apply (cancel_mono ((derivedComplexCompletionUnit R a).app Z)).mp
  have hg := (derivedComplexCompletionUnit R a).naturality g
  have hh := (derivedComplexCompletionUnit R a).naturality h
  simp only [Functor.id_map] at hg hh
  rw [hg, hh, hm]

/-- The same uniqueness criterion inside the bounded-above category. -/
theorem boundedAboveCompletionEquivalence_hom_ext
    {X Y Z : D} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom))
    (hZ : IsComplete R a Z.obj) {g h : Y ⟶ Z} (he : f ≫ g = f ≫ h) : g = h := by
  apply InducedCategory.hom_ext
  apply completionEquivalence_hom_ext R a f.hom hf hZ
  exact congrArg (fun k ↦ k.hom) he

/-- The canonical comparison is natural in both tensor factors. -/
theorem boundedAboveCompletionTensorComparison_naturality
    {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((boundedAboveDerivedCompletionFunctor R a).map f ⊗ₘ
      (boundedAboveDerivedCompletionFunctor R a).map g) ≫
        boundedAboveCompletionTensorComparison R a X' Y' =
      boundedAboveCompletionTensorComparison R a X Y ≫
        (boundedAboveDerivedCompletionFunctor R a).map (f ⊗ₘ g) := by
  let η := boundedAboveDerivedCompletionUnit R a
  let L := boundedAboveDerivedCompletionFunctor R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (η.app X ⊗ₘ η.app Y)
    (completionEquivalence_tensorHom R a _ _
      (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
      (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj))
    (derivedComplexCompletionFunctor_isComplete R a (X' ⊗ Y').obj)
  have hf := η.naturality f
  have hg := η.naturality g
  simp only [Functor.id_map] at hf hg
  have ht : (η.app X ⊗ₘ η.app Y) ≫ (L.map f ⊗ₘ L.map g) =
      (f ⊗ₘ g) ≫ (η.app X' ⊗ₘ η.app Y') := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ← hf, ← hg]
  rw [← Category.assoc, ht, Category.assoc, boundedAboveCompletionTensorComparison_unit,
    ← Category.assoc, boundedAboveCompletionTensorComparison_unit]
  exact η.naturality (f ⊗ₘ g)

end SerrePositivity.DerivedCompletion

end CompletionTensorComparisonPart

section CompletionTensorCoherencePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)
local notation "μ" => boundedAboveCompletionTensorComparison R a

/-- The completion tensor comparison respects the actual associator. -/
theorem boundedAboveCompletionTensorComparison_assoc (X Y Z : D) :
    (μ X Y ⊗ₘ 𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj Z)) ≫
      μ (X ⊗ Y) Z ≫ (boundedAboveDerivedCompletionFunctor R a).map (α_ X Y Z).hom =
    (α_ ((boundedAboveDerivedCompletionFunctor R a).obj X)
      ((boundedAboveDerivedCompletionFunctor R a).obj Y)
      ((boundedAboveDerivedCompletionFunctor R a).obj Z)).hom ≫
      (𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X) ⊗ₘ μ Y Z) ≫
        μ X (Y ⊗ Z) := by
  let η := boundedAboveDerivedCompletionUnit R a
  have htXY := completionEquivalence_tensorHom R a (η.app X) (η.app Y)
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
    (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj)
  apply boundedAboveCompletionEquivalence_hom_ext R a
    ((η.app X ⊗ₘ η.app Y) ⊗ₘ η.app Z)
    (completionEquivalence_tensorHom R a _ _ htXY
      (derivedComplexCompletionFunctor_map_unit_isIso R a Z.obj))
    (derivedComplexCompletionFunctor_isComplete R a (X ⊗ (Y ⊗ Z)).obj)
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, boundedAboveCompletionTensorComparison_unit]
  rw [associator_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (η.app X ⊗ₘ (η.app Y ⊗ₘ η.app Z)),
    tensorHom_comp_tensorHom, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, boundedAboveCompletionTensorComparison_unit]
  exact (η.naturality (α_ X Y Z).hom).symm

/-- The completion tensor comparison respects the actual symmetry. -/
theorem boundedAboveCompletionTensorComparison_braiding (X Y : D) :
    (β_ ((boundedAboveDerivedCompletionFunctor R a).obj X)
      ((boundedAboveDerivedCompletionFunctor R a).obj Y)).hom ≫ μ Y X =
    μ X Y ≫ (boundedAboveDerivedCompletionFunctor R a).map (β_ X Y).hom := by
  let η := boundedAboveDerivedCompletionUnit R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (η.app X ⊗ₘ η.app Y)
    (completionEquivalence_tensorHom R a _ _
      (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj)
      (derivedComplexCompletionFunctor_map_unit_isIso R a Y.obj))
    (derivedComplexCompletionFunctor_isComplete R a (Y ⊗ X).obj)
  rw [← Category.assoc, BraidedCategory.braiding_naturality, Category.assoc,
    boundedAboveCompletionTensorComparison_unit, ← Category.assoc,
    boundedAboveCompletionTensorComparison_unit]
  exact η.naturality (β_ X Y).hom

/-- The standard completion unit supplies the left unit of the tensor comparison. -/
theorem boundedAboveCompletionTensorComparison_left_unitality (X : D) :
    (λ_ ((boundedAboveDerivedCompletionFunctor R a).obj X)).hom =
      ((boundedAboveDerivedCompletionUnit R a).app (𝟙_ D) ⊗ₘ
        𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X)) ≫
      μ (𝟙_ D) X ≫ (boundedAboveDerivedCompletionFunctor R a).map (λ_ X).hom := by
  let η := boundedAboveDerivedCompletionUnit R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (𝟙 (𝟙_ D) ⊗ₘ η.app X)
    (completionEquivalence_tensorHom R a _ _ (by
      change IsIso ((derivedComplexCompletionFunctor R a).map (𝟙 (𝟙_ D).obj))
      infer_instance) (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj))
    (derivedComplexCompletionFunctor_isComplete R a X.obj)
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, id_tensorHom, leftUnitor_naturality]
  exact η.naturality (λ_ X).hom

/-- The standard completion unit supplies the right unit of the tensor comparison. -/
theorem boundedAboveCompletionTensorComparison_right_unitality (X : D) :
    (ρ_ ((boundedAboveDerivedCompletionFunctor R a).obj X)).hom =
      (𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X) ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app (𝟙_ D)) ≫
      μ X (𝟙_ D) ≫ (boundedAboveDerivedCompletionFunctor R a).map (ρ_ X).hom := by
  let η := boundedAboveDerivedCompletionUnit R a
  apply boundedAboveCompletionEquivalence_hom_ext R a (η.app X ⊗ₘ 𝟙 (𝟙_ D))
    (completionEquivalence_tensorHom R a _ _
      (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) (by
        change IsIso ((derivedComplexCompletionFunctor R a).map (𝟙 (𝟙_ D).obj))
        infer_instance))
    (derivedComplexCompletionFunctor_isComplete R a X.obj)
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
    boundedAboveCompletionTensorComparison_unit, tensorHom_id, rightUnitor_naturality]
  exact η.naturality (ρ_ X).hom

/-- Actual principal derived completion is lax monoidal via its canonical comparison. -/
@[instance_reducible] def boundedAboveDerivedCompletionLaxMonoidal :
    (boundedAboveDerivedCompletionFunctor R a).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    ((boundedAboveDerivedCompletionUnit R a).app (𝟙_ D))
    (boundedAboveCompletionTensorComparison R a)
    (fun f g ↦ boundedAboveCompletionTensorComparison_naturality R a f g)
    (boundedAboveCompletionTensorComparison_assoc R a)
    (boundedAboveCompletionTensorComparison_left_unitality R a)
    (boundedAboveCompletionTensorComparison_right_unitality R a)

/-- The canonical lax structure also preserves the actual braiding. -/
@[instance_reducible] def boundedAboveDerivedCompletionLaxBraided :
    (boundedAboveDerivedCompletionFunctor R a).LaxBraided where
  toLaxMonoidal := boundedAboveDerivedCompletionLaxMonoidal R a
  braided X Y := (boundedAboveCompletionTensorComparison_braiding R a X Y).symm

/-- The original standard unit is monoidal for the canonical completion tensor structure. -/
theorem boundedAboveDerivedCompletionUnitMonoidal :
    letI := boundedAboveDerivedCompletionLaxMonoidal R a
    NatTrans.IsMonoidal (boundedAboveDerivedCompletionUnit R a) := by
  let := boundedAboveDerivedCompletionLaxMonoidal R a
  constructor
  · exact Category.id_comp _
  · intro X Y
    change 𝟙 (X ⊗ Y) ≫ (boundedAboveDerivedCompletionUnit R a).app (X ⊗ Y) =
      ((boundedAboveDerivedCompletionUnit R a).app X ⊗ₘ
        (boundedAboveDerivedCompletionUnit R a).app Y) ≫ μ X Y
    rw [Category.id_comp, boundedAboveCompletionTensorComparison_unit]

end SerrePositivity.DerivedCompletion

end CompletionTensorCoherencePart

section CompletionAlgebraObjectsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Complete actual commutative algebra objects using the proved canonical lax structure. -/
def boundedAboveCompletionCommMonFunctor : CommMon D ⥤ CommMon D := by
  letI := boundedAboveDerivedCompletionLaxBraided R a
  exact (boundedAboveDerivedCompletionFunctor R a).mapCommMon

/-- The completed algebra unit uses the original standard completion unit. -/
theorem boundedAboveCompletionCommMonFunctor_one (A : CommMon D) :
    ((boundedAboveCompletionCommMonFunctor R a).obj A).mon.one =
      (boundedAboveDerivedCompletionUnit R a).app (𝟙_ D) ≫
        (boundedAboveDerivedCompletionFunctor R a).map A.mon.one := rfl

/-- The standard completion unit itself is a morphism of actual commutative algebra objects. -/
def boundedAboveCompletionAlgebraUnit (A : CommMon D) :
    A ⟶ (boundedAboveCompletionCommMonFunctor R a).obj A := by
  letI := boundedAboveDerivedCompletionLaxBraided R a
  letI : NatTrans.IsMonoidal (boundedAboveDerivedCompletionUnit R a) :=
    boundedAboveDerivedCompletionUnitMonoidal R a
  exact (Functor.mapCommMonIdIso (C := D)).inv.app A ≫
    (Functor.mapCommMonNatTrans (boundedAboveDerivedCompletionUnit R a)).app A

/-- Forgetting the algebra structure recovers the existing standard unit exactly. -/
theorem boundedAboveCompletionAlgebraUnit_hom (A : CommMon D) :
    (boundedAboveCompletionAlgebraUnit R a A).hom.hom =
      (boundedAboveDerivedCompletionUnit R a).app A.X := by
  change 𝟙 A.X ≫ (boundedAboveDerivedCompletionUnit R a).app A.X = _
  exact Category.id_comp _

/-- Completion on algebra morphisms uses the original derived completion map. -/
theorem boundedAboveCompletionCommMonFunctor_map_hom {A B : CommMon D} (f : A ⟶ B) :
    ((boundedAboveCompletionCommMonFunctor R a).map f).hom.hom =
      (boundedAboveDerivedCompletionFunctor R a).map f.hom.hom := rfl

/-- The standard algebra completion unit is natural in all algebra morphisms. -/
theorem boundedAboveCompletionAlgebraUnit_naturality {A B : CommMon D} (f : A ⟶ B) :
    f ≫ boundedAboveCompletionAlgebraUnit R a B =
      boundedAboveCompletionAlgebraUnit R a A ≫
        (boundedAboveCompletionCommMonFunctor R a).map f := by
  apply CommMon.hom_ext
  change f.hom.hom ≫ (boundedAboveCompletionAlgebraUnit R a B).hom.hom =
    (boundedAboveCompletionAlgebraUnit R a A).hom.hom ≫
      ((boundedAboveCompletionCommMonFunctor R a).map f).hom.hom
  rw [boundedAboveCompletionAlgebraUnit_hom, boundedAboveCompletionAlgebraUnit_hom,
    boundedAboveCompletionCommMonFunctor_map_hom]
  exact (boundedAboveDerivedCompletionUnit R a).naturality f.hom.hom

/-- The actual completed derived tensor, with its canonical commutative algebra structure. -/
def boundedAboveCompletedTensorAlgebra
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] : CommMon D :=
  (boundedAboveCompletionCommMonFunctor R a).obj (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- The standard left factor map into the completed tensor is an algebra morphism. -/
def boundedAboveCompletedTensorAlgebraLeft
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedAlgebra (R := R) S ⟶ boundedAboveCompletedTensorAlgebra R a S T :=
  boundedAboveDerivedTensorAlgebraLeft (R := R) S T ≫
    boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- The standard right factor map into the completed tensor is an algebra morphism. -/
def boundedAboveCompletedTensorAlgebraRight
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveDerivedAlgebra (R := R) T ⟶ boundedAboveCompletedTensorAlgebra R a S T :=
  boundedAboveDerivedTensorAlgebraRight (R := R) S T ≫
    boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- The completed actual standard augmentation is a commutative algebra morphism. -/
def boundedAboveCompletedTensorAlgebraAugmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletedTensorAlgebra R a S T ⟶
      (boundedAboveCompletionCommMonFunctor R a).obj
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) :=
  (boundedAboveCompletionCommMonFunctor R a).map
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T)

/-- The original standard augmentation diagram remains an algebra diagram after completion. -/
theorem boundedAboveCompletedTensorAlgebraAugmentation_unit
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra (R := R) S T) ≫
        boundedAboveCompletedTensorAlgebraAugmentation R a S T =
      boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T ≫
        boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) :=
  (boundedAboveCompletionAlgebraUnit_naturality R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T)).symm

/-- The left factor agrees with the ordinary tensor inclusion after completed augmentation. -/
theorem boundedAboveCompletedTensorAlgebraLeft_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletedTensorAlgebraLeft R a S T ≫
        boundedAboveCompletedTensorAlgebraAugmentation R a S T =
      boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T) ≫
        boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) := by
  rw [boundedAboveCompletedTensorAlgebraLeft, Category.assoc,
    boundedAboveCompletedTensorAlgebraAugmentation_unit, ← Category.assoc,
    boundedAboveDerivedTensorAlgebraLeft_augmentation]

/-- The right factor agrees with the ordinary tensor inclusion after completed augmentation. -/
theorem boundedAboveCompletedTensorAlgebraRight_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    boundedAboveCompletedTensorAlgebraRight R a S T ≫
        boundedAboveCompletedTensorAlgebraAugmentation R a S T =
      boundedAboveDerivedAlgebraMap (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T) ≫
        boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)) := by
  rw [boundedAboveCompletedTensorAlgebraRight, Category.assoc,
    boundedAboveCompletedTensorAlgebraAugmentation_unit, ← Category.assoc,
    boundedAboveDerivedTensorAlgebraRight_augmentation]

end SerrePositivity.DerivedCompletion

end CompletionAlgebraObjectsPart

section CompletionH0AlgebraPart

namespace SerrePositivity
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Evaluation of composition uses the original actual H⁰ maps. -/
lemma derivedH0AlgMap_comp_apply
    {A B C : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))}
    (f : A ⟶ B) (g : B ⟶ C)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap g (derivedH0AlgMap f x) = derivedH0AlgMap (f ≫ g) x := by
  rw [derivedH0AlgMap_apply, derivedH0AlgMap_apply, derivedH0AlgMap_apply]
  change (DerivedCategory.homologyFunctor (ModuleCat R) 0).map g.hom.hom.hom
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x) =
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map (f.hom.hom.hom ≫ g.hom.hom.hom) x
  rw [CategoryTheory.Functor.map_comp]
  rfl

namespace DerivedCompletion
variable (R) (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- The H⁰ algebra completion map is the H⁰ map of the original standard completion unit. -/
lemma completionH0AlgebraUnit_apply (A : CommMon D)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A) x =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionUnit R a).app A.X).hom x := by
  rw [derivedH0AlgMap_apply, boundedAboveCompletionAlgebraUnit_hom]
  rfl

/-- The actual H⁰ algebra completion maps satisfy the standard unit naturality square. -/
lemma completionH0AlgebraUnit_naturality {A B : CommMon D} (f : A ⟶ B)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgMap ((boundedAboveCompletionCommMonFunctor R a).map f)
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a B) (derivedH0AlgMap f x) := by
  rw [derivedH0AlgMap_comp_apply, derivedH0AlgMap_comp_apply,
    boundedAboveCompletionAlgebraUnit_naturality]

/-- The original augmentation and completion unit square commutes as actual H⁰ algebra maps. -/
lemma completedTensorH0AlgebraAugmentation_unit
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
        (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
          (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x) := by
  exact completionH0AlgebraUnit_naturality R a
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T) x

/-- The completed left factor agrees with the completed ordinary inclusion. -/
lemma completedTensorH0AlgebraLeft_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) S).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraLeft R a S T) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)) x) := by
  rw [derivedH0AlgMap_comp_apply, derivedH0AlgMap_comp_apply,
    boundedAboveCompletedTensorAlgebraLeft_augmentation]

/-- The completed right factor agrees with the completed ordinary inclusion. -/
lemma completedTensorH0AlgebraRight_augmentation
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedAlgebra (R := R) T).X.obj) :
    derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
        (derivedH0AlgMap (boundedAboveCompletedTensorAlgebraRight R a S T) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)))
        (derivedH0AlgMap (boundedAboveDerivedAlgebraMap
          (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)) x) := by
  rw [derivedH0AlgMap_comp_apply, derivedH0AlgMap_comp_apply,
    boundedAboveCompletedTensorAlgebraRight_augmentation]

end DerivedCompletion
end SerrePositivity

end CompletionH0AlgebraPart

section CompletionH0AlgebraUniversalPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
section LinearExtension
variable (R B C T : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing T]
    [Algebra R B] [Algebra R C] [Algebra R T]
/-- A linearly dense algebra unit makes every compatible linear extension multiplicative. -/
def algHomOfDenseLinearExtension (j : B →ₐ[R] C) (f : B →ₐ[R] T) (g : C →ₗ[R] T)
    (hg : ∀ b, g (j b) = f b)
    (hd : Function.Injective (fun l : C →ₗ[R] T => l.comp j.toLinearMap)) : C →ₐ[R] T := by
  apply AlgHom.ofLinearMap g
  · simpa only [map_one] using hg 1
  · intro x y
    have hleft (b : B) : g.comp (LinearMap.mulLeft R (j b)) =
        (LinearMap.mulLeft R (f b)).comp g := by
      apply hd
      apply LinearMap.ext
      intro z
      change g (j b * j z) = f b * g (j z)
      rw [← map_mul j, hg, hg, map_mul f]
    have hright (y : C) : g.comp (LinearMap.mulRight R y) =
        (LinearMap.mulRight R (g y)).comp g := by
      apply hd
      apply LinearMap.ext
      intro b
      change g (j b * y) = g (j b) * g y
      rw [hg]
      exact LinearMap.congr_fun (hleft b) y
    exact LinearMap.congr_fun (hright y) x
end LinearExtension
variable (R : Type u) [CommRing R] (a : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) [A.X.obj.IsLE 0]
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsModuleComplete R a (ModuleCat.of R T))
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "HC" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A)

include hT in
/-- Linear maps out of actual completed H⁰ are determined by the original algebra unit. -/
theorem completionH0_linear_ext :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    Function.Injective (fun g : HC →ₗ[R] T => g.comp (J).toLinearMap) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro g k hg
  have he : completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT (ModuleCat.ofHom g) =
      completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT (ModuleCat.ofHom k) := by
    rw [completionH0HomEquiv_apply, completionH0HomEquiv_apply]
    ext x
    have hx := LinearMap.congr_fun hg x
    change g ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R a).app A.X.obj) x) =
      k ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app A.X.obj) x)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      completionH0AlgebraUnit_apply, boundedAboveDerivedCompletionUnit,
      ObjectProperty.homMk] at hx
    exact hx
  exact congrArg (fun f => f.hom) ((completionH0HomEquiv R a A.X.obj
    (ModuleCat.of R T) hT).injective he)

/-- Extend an algebra map across the original actual H⁰ completion unit. -/
def completionH0AlgebraLift :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    (H →ₐ[R] T) → (HC →ₐ[R] T) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro f
  let g := (completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).symm
    (ModuleCat.ofHom f.toLinearMap)
  have hg (x : H) : g.hom (J x) = f x := by
    have he := (completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).apply_symm_apply
      (ModuleCat.ofHom f.toLinearMap)
    rw [completionH0HomEquiv_apply] at he
    have hx := congrArg (fun l => l.hom x) he
    change g.hom ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R a).app A.X.obj) x) = f x at hx
    rw [completionH0AlgebraUnit_apply]
    exact hx
  exact algHomOfDenseLinearExtension R H HC T J f g.hom hg
    (completionH0_linear_ext R a A T hT)

/-- The extension retains the original completion-unit diagram. -/
lemma completionH0AlgebraLift_unit :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    ∀ (f : H →ₐ[R] T), (completionH0AlgebraLift R a A T hT f).comp J = f := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro f
  ext x
  have he := (completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).apply_symm_apply
    (ModuleCat.ofHom f.toLinearMap)
  rw [completionH0HomEquiv_apply] at he
  have hx := congrArg (fun l => l.hom x) he
  change ((completionH0HomEquiv R a A.X.obj (ModuleCat.of R T) hT).symm
    (ModuleCat.ofHom f.toLinearMap)).hom (J x) = f x
  rw [completionH0AlgebraUnit_apply]
  exact hx

include hT in
/-- Actual completed H⁰ is universal as an algebra, not merely as a module. -/
theorem completionH0_existsUnique_algHom :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    ∀ (f : H →ₐ[R] T), ∃! g : HC →ₐ[R] T, g.comp J = f := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  intro f
  refine ⟨completionH0AlgebraLift R a A T hT f, completionH0AlgebraLift_unit R a A T hT f, ?_⟩
  intro g hg
  apply AlgHom.toLinearMap_injective
  apply completionH0_linear_ext R a A T hT
  exact congrArg AlgHom.toLinearMap (hg.trans
    (completionH0AlgebraLift_unit R a A T hT f).symm)

end SerrePositivity.DerivedCompletion

end CompletionH0AlgebraUniversalPart

section CompletionPointActionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- A point-action map induces exactly multiplication in the actual H⁰ ring. -/
lemma derivedH0_pointAction
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    (x y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    letI := derivedH0CommRing A
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (commMonPointAction A (boundedAboveUnitH0LinearEquiv A.X x)).hom y = x * y := by
  let := derivedH0CommRing A
  let := commMonUnitHomCommRing (DerivedCategory.Minus (ModuleCat R)) A
  apply (boundedAboveUnitH0LinearEquiv A.X).injective
  rw [boundedAboveUnitH0LinearEquiv_naturality]
  exact (commMonPointAction_sections A _ _).trans
    ((derivedH0UnitHomRingEquiv A).map_mul x y).symm

namespace DerivedCompletion
variable (R) (a : R)

/-- Completing the actual point-action map gives multiplication by its original unit-image. -/
lemma boundedAboveCompletion_pointAction
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    (p : 𝟙_ (DerivedCategory.Minus (ModuleCat R)) ⟶ A.X) :
    (boundedAboveDerivedCompletionFunctor R a).map (commMonPointAction A p) =
      commMonPointAction ((boundedAboveCompletionCommMonFunctor R a).obj A)
        (p ≫ (boundedAboveCompletionAlgebraUnit R a A).hom.hom) := by
  rw [boundedAboveCompletionAlgebraUnit_hom]
  apply InducedCategory.hom_ext
  apply derivedComplexCompletionHom_ext R a
    (derivedComplexCompletionFunctor_isComplete R a A.X.obj)
  have hn := (boundedAboveDerivedCompletionUnit R a).naturality (commMonPointAction A p)
  simp only [CategoryTheory.Functor.id_map] at hn
  have hm := commMonPointAction_naturality (boundedAboveCompletionAlgebraUnit R a A) p
  rw [boundedAboveCompletionAlgebraUnit_hom] at hm
  exact congrArg (fun f ↦ f.hom) (hn.symm.trans hm)

/-- The completed point-action acts on actual H⁰ by multiplication by the original H⁰ unit-image. -/
lemma boundedAboveCompletion_pointAction_homology
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj) :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (commMonPointAction A (boundedAboveUnitH0LinearEquiv A.X x))).hom y =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A) x * y := by
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  rw [boundedAboveCompletion_pointAction, derivedH0AlgMap_apply]
  have hx := boundedAboveUnitH0LinearEquiv_naturality
    (X := A.X) (Y := ((boundedAboveCompletionCommMonFunctor R a).obj A).X)
    (boundedAboveCompletionAlgebraUnit R a A).hom.hom x
  rw [← hx]
  exact derivedH0_pointAction _ _ _

/-- Ordinary coefficient multiplication completes to multiplication by its standard H⁰ image. -/
lemma boundedAboveCompletion_discrete_mul_homology
    (A : Type u) [CommRing A] [Algebra R A] (b : A)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj
        (boundedAboveDerivedAlgebra (R := R) A)).X.obj) :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj
      (boundedAboveDerivedAlgebra (R := R) A))
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))).hom y =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) A))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R A) b) * y := by
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) A))
  have h := boundedAboveCompletion_pointAction_homology R a
    (boundedAboveDerivedAlgebra (R := R) A)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R A) b) y
  rw [boundedAboveDerivedAlgebra_pointAction_singleH0] at h
  exact h

/-- Over the coefficient ring itself, completed multiplication is its original scalar action. -/
lemma boundedAboveCompletion_coefficient_smul_homology (r : R)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj
        (boundedAboveDerivedAlgebra (R := R) R)).X.obj) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R r)))).hom y =
      r • y := by
  let : CommRing ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) R)
  let : Algebra R ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) R)
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) R))
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) R))
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) R)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) R)
  have hr : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R R) r = algebraMap R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) r :=
    (derivedSingleH0AlgEquiv (R := R) R).symm.commutes r
  have h := boundedAboveCompletion_discrete_mul_homology R a R r y
  erw [hr, AlgHom.commutes] at h
  exact h.trans (Algebra.smul_def r y).symm

end DerivedCompletion
end SerrePositivity

end CompletionPointActionPart
