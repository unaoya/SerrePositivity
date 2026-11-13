import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor
import SerrePositivity.InfinityCategories.Derived.HeartFullyFaithful

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

abbrev DVertex := (derivedInfinityCategory R) _⦋0⦌

def completedModuleTensor (a : R) (X Y : DVertex R) : DVertex R :=
  let C := DerivedCategory.Q.obj (cochainTensor (X.obj 0).val (Y.obj 0).val)
  ((derivedInfinityHomotopyEquivalence R).inverse.obj
    ((derivedComplexCompletionFunctor R a).obj C)).pt

def heartModel (M : ModuleCat.{u} R) :
    BoundedAboveDerivedModel ((boundedAboveDerivedSingleFunctor.obj M).obj) where
  complex := (moduleFreeCochainResolution R).obj M
  bound := 0
  bounded := (CochainComplex.isStrictlyLE_iff _ _).mpr (fun k hk =>
    moduleFreeCochainResolution_isZero R M k hk)
  projective i := by
    let := moduleFreeCochainResolution_free R M i
    infer_instance
  iso := by
    letI := moduleFreeCochainAugmentation_quasiIso R M
    exact asIso (DerivedCategory.Q.map (moduleFreeCochainAugmentation R M))

def compareTensor (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (boundedAboveCompletedTensorAlgebra R a S T).X.obj ≅
      (derivedInfinityHomotopyEquivalence R).functor.obj
        ⟨completedModuleTensor R a (moduleHeartVertex R (ModuleCat.of R S))
          (moduleHeartVertex R (ModuleCat.of R T))⟩ := by
  let e := derivedInfinityHomotopyEquivalence R
  exact (derivedComplexCompletionFunctor R a).mapIso
      (boundedAboveDerivedTensorModelIso _ _ (heartModel R (ModuleCat.of R S))
        (heartModel R (ModuleCat.of R T))) ≪≫
    (e.counitIso.app _).symm

#print axioms compareTensor

def compareModuleTensor (a : R) (M N : ModuleCat.{u} R) :
    ((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj (boundedAboveDerivedSingleFunctor.obj M,
        boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      (derivedComplexCompletionFunctor R a).obj
        (DerivedCategory.Q.obj (cochainTensor ((moduleFreeCochainResolution R).obj M)
          ((moduleFreeCochainResolution R).obj N))) :=
  (derivedComplexCompletionFunctor R a).mapIso
    (boundedAboveDerivedTensorModelIso _ _ (heartModel R M) (heartModel R N))

theorem compareModuleTensor_naturality (a : R) {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((boundedAboveDerivedCompletionFunctor R a).map
      (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g)))).hom ≫
      (compareModuleTensor R a M' N').hom =
    (compareModuleTensor R a M N).hom ≫
      (derivedComplexCompletionFunctor R a).map (DerivedCategory.Q.map
        (cochainTensorMap ((moduleFreeCochainResolution R).map f)
          ((moduleFreeCochainResolution R).map g))) := by
  have represent {A B : ModuleCat.{u} R} (h : A ⟶ B) :
      DerivedCategory.Q.map ((moduleFreeCochainResolution R).map h) ≫ (heartModel R B).iso.hom =
        (heartModel R A).iso.hom ≫ (boundedAboveDerivedSingleFunctor.map h).hom := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      (moduleFreeCochainAugmentationNat R).naturality]
  change (derivedComplexCompletionFunctor R a).map _ ≫ (derivedComplexCompletionFunctor R a).map _ =
    (derivedComplexCompletionFunctor R a).map _ ≫ (derivedComplexCompletionFunctor R a).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (derivedComplexCompletionFunctor R a).map
    (boundedAboveDerivedTensorModelIso_naturality
      (heartModel R M) (heartModel R M') (heartModel R N) (heartModel R N')
      (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g)
      ((moduleFreeCochainResolution R).map f) ((moduleFreeCochainResolution R).map g)
      (represent f) (represent g))

open MonoidalCategory

private lemma completedTensorLeft_comparison (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (uT : cochainTensorUnit (R := R) ⟶ (moduleFreeCochainResolution R).obj (ModuleCat.of R T))
    (huT : DerivedCategory.Q.map uT ≫ (heartModel R (ModuleCat.of R T)).iso.hom =
      (boundedAboveDerivedAlgebraUnit (R := R) T).hom) :
    (boundedAboveCompletedTensorAlgebraLeft R a S T).hom.hom.hom ≫
      (compareModuleTensor R a (ModuleCat.of R S) (ModuleCat.of R T)).hom =
    (heartModel R (ModuleCat.of R S)).iso.inv ≫
      DerivedCategory.Q.map (cochainTensorRightUnitor
        ((moduleFreeCochainResolution R).obj (ModuleCat.of R S))).inv ≫
      DerivedCategory.Q.map (cochainTensorMap
        (𝟙 ((moduleFreeCochainResolution R).obj (ModuleCat.of R S))) uT) ≫
      (derivedComplexCompletionUnit R a).app _ := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)
  let P := heartModel R (ModuleCat.of R S)
  let Q := heartModel R (ModuleCat.of R T)
  let U := boundedAboveDerivedTensorUnit (R := R)
  let UP := boundedAboveDerivedTensorUnitModel (R := R)
  let C := derivedComplexCompletionFunctor R a
  let η := derivedComplexCompletionUnit R a
  let f := boundedAboveDerivedAlgebraUnit (R := R) T
  let k := cochainTensorMap (𝟙 P.complex) uT
  let modelIso := boundedAboveDerivedTensorModelIso X Y P Q
  have hn := boundedAboveDerivedTensorModelIso_naturality P P UP Q
    (𝟙 X) f (𝟙 P.complex) uT (by
      change DerivedCategory.Q.map (𝟙 P.complex) ≫ P.iso.hom = P.iso.hom ≫ 𝟙 X.obj
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]) (by simpa [UP, boundedAboveDerivedTensorUnitModel] using huT)
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) f)).hom ≫
    modelIso.hom = (boundedAboveDerivedTensorModelIso X U P UP).hom ≫
      DerivedCategory.Q.map k at hn
  have hunit := boundedAboveDerivedRightUnitor_models X P
  have hunit' :
      (boundedAboveDerivedTensorRightUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorModelIso X U P UP).hom =
        P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).inv := by
    calc
      _ = (boundedAboveDerivedTensorRightUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorRightUnitor X).hom.hom ≫ P.iso.inv ≫
          DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).inv := by
            rw [hunit]
            simp [← Functor.map_comp]
            rfl
      _ = _ := by
        change (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorRightUnitor X)).inv ≫
          (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorRightUnitor X)).hom ≫
          P.iso.inv ≫ _ = _
        simp
  have hl : (boundedAboveCompletedTensorAlgebraLeft R a S T).hom.hom.hom =
      (boundedAboveDerivedTensorRightUnitor X).inv.hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) f)).hom ≫ η.app _ := by
    change ((boundedAboveDerivedTensorAlgebraLeft S T).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra S T)).hom.hom).hom = _
    rw [ObjectProperty.FullSubcategory.comp_hom, boundedAboveCompletionAlgebraUnit_hom,
      boundedAboveDerivedTensorAlgebraLeft_hom, ObjectProperty.FullSubcategory.comp_hom,
      Category.assoc]
    rfl
  change (boundedAboveCompletedTensorAlgebraLeft R a S T).hom.hom.hom ≫ C.map modelIso.hom =
    P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).inv ≫
      DerivedCategory.Q.map k ≫ η.app _
  rw [hl, Category.assoc, Category.assoc, ← η.naturality, Functor.id_map,
    ← Category.assoc ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) f)).hom),
    hn]
  simp only [Category.assoc, reassoc_of% hunit']
  rfl

#print axioms compareModuleTensor_naturality
#print axioms completedTensorLeft_comparison

theorem exists_heartUnitLift (T : Type u) [CommRing T] [Algebra R T] :
    ∃ uT : cochainTensorUnit (R := R) ⟶ (moduleFreeCochainResolution R).obj (ModuleCat.of R T),
      DerivedCategory.Q.map uT ≫ (heartModel R (ModuleCat.of R T)).iso.hom =
        (boundedAboveDerivedAlgebraUnit (R := R) T).hom := by
  let U := boundedAboveDerivedTensorUnitModel (R := R)
  let P := heartModel R (ModuleCat.of R T)
  have h := U.map_naturality P (boundedAboveDerivedAlgebraUnit (R := R) T).hom
  exact ⟨_, by simpa [U, boundedAboveDerivedTensorUnitModel] using h⟩

private lemma completedTensorRight_comparison (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (uT : cochainTensorUnit (R := R) ⟶ (moduleFreeCochainResolution R).obj (ModuleCat.of R T))
    (huT : DerivedCategory.Q.map uT ≫ (heartModel R (ModuleCat.of R T)).iso.hom =
      (boundedAboveDerivedAlgebraUnit (R := R) T).hom) :
    (boundedAboveCompletedTensorAlgebraRight R a T S).hom.hom.hom ≫
      (compareModuleTensor R a (ModuleCat.of R T) (ModuleCat.of R S)).hom =
    (heartModel R (ModuleCat.of R S)).iso.inv ≫
      DerivedCategory.Q.map (cochainTensorLeftUnitor
        ((moduleFreeCochainResolution R).obj (ModuleCat.of R S))).inv ≫
      DerivedCategory.Q.map (cochainTensorMap
        uT (𝟙 ((moduleFreeCochainResolution R).obj (ModuleCat.of R S)))) ≫
      (derivedComplexCompletionUnit R a).app _ := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)
  let P := heartModel R (ModuleCat.of R S)
  let Q := heartModel R (ModuleCat.of R T)
  let U := boundedAboveDerivedTensorUnit (R := R)
  let UP := boundedAboveDerivedTensorUnitModel (R := R)
  let C := derivedComplexCompletionFunctor R a
  let η := derivedComplexCompletionUnit R a
  let f := boundedAboveDerivedAlgebraUnit (R := R) T
  let k := cochainTensorMap uT (𝟙 P.complex)
  let modelIso := boundedAboveDerivedTensorModelIso Y X Q P
  have hn := boundedAboveDerivedTensorModelIso_naturality UP Q P P
    f (𝟙 X) uT (𝟙 P.complex) (by simpa [UP, boundedAboveDerivedTensorUnitModel] using huT)
    (by
      change DerivedCategory.Q.map (𝟙 P.complex) ≫ P.iso.hom = P.iso.hom ≫ 𝟙 X.obj
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom f (𝟙 X))).hom ≫
    modelIso.hom = (boundedAboveDerivedTensorModelIso U X UP P).hom ≫
      DerivedCategory.Q.map k at hn
  have hunit := boundedAboveDerivedLeftUnitor_models X P
  have hunit' :
      (boundedAboveDerivedTensorLeftUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorModelIso U X UP P).hom =
        P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).inv := by
    calc
      _ = (boundedAboveDerivedTensorLeftUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorLeftUnitor X).hom.hom ≫ P.iso.inv ≫
          DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).inv := by
            rw [hunit]
            simp [← Functor.map_comp]
            rfl
      _ = _ := by
        change (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorLeftUnitor X)).inv ≫
          (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorLeftUnitor X)).hom ≫
          P.iso.inv ≫ _ = _
        simp
  have hl : (boundedAboveCompletedTensorAlgebraRight R a T S).hom.hom.hom =
      (boundedAboveDerivedTensorLeftUnitor X).inv.hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom f (𝟙 X))).hom ≫ η.app _ := by
    change ((boundedAboveDerivedTensorAlgebraRight T S).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedTensorAlgebra T S)).hom.hom).hom = _
    rw [ObjectProperty.FullSubcategory.comp_hom, boundedAboveCompletionAlgebraUnit_hom,
      boundedAboveDerivedTensorAlgebraRight_hom, ObjectProperty.FullSubcategory.comp_hom,
      Category.assoc]
    rfl
  change (boundedAboveCompletedTensorAlgebraRight R a T S).hom.hom.hom ≫ C.map modelIso.hom =
    P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).inv ≫
      DerivedCategory.Q.map k ≫ η.app _
  rw [hl, Category.assoc, Category.assoc, ← η.naturality, Functor.id_map,
    ← Category.assoc ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom f (𝟙 X))).hom),
    hn]
  simp only [Category.assoc, reassoc_of% hunit']
  rfl

#print axioms completedTensorRight_comparison
