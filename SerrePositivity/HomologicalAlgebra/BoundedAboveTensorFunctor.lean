module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveResolutionFunctor
public import SerrePositivity.HomologicalAlgebra.BoundedAboveTensorModels

/-! # Derived tensor models as a functor on bounded-above complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Tensoring quasi-isomorphisms between K-projective complexes preserves quasi-isomorphisms. -/
lemma cochainTensorMap_quasiIso_of_KProjective
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    [P.IsKProjective] [P'.IsKProjective] [Q.IsKProjective] [Q'.IsKProjective]
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (cochainTensorMap f g) := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  obtain ⟨e', he'⟩ := (CochainComplex.IsKProjective.quasiIso_iff g).mp inferInstance
  have h : (cochainTensorHomotopyEquiv e e').hom = cochainTensorMap f g := by
    simp [cochainTensorHomotopyEquiv, he, he']
  rw [← h]
  infer_instance

/-- Derived tensor on bounded-above complexes. All map laws hold in the actual derived category. -/
def boundedAboveDerivedTensorFunctor :
    (BoundedAboveCochain (ModuleCat.{u} R) × BoundedAboveCochain (ModuleCat.{u} R)) ⥤
      DerivedCategory (ModuleCat.{u} R) where
  obj K := (boundedAboveChosenResolution K.1).derivedTensorModel
    (boundedAboveChosenResolution K.2)
  map {K L} f := DerivedCategory.Q.map (cochainTensorMap
    ((boundedAboveChosenResolution K.1).map (boundedAboveChosenResolution L.1) f.1.hom)
    ((boundedAboveChosenResolution K.2).map (boundedAboveChosenResolution L.2) f.2.hom))
  map_id K := by
    let P := boundedAboveChosenResolution K.1
    let Q := boundedAboveChosenResolution K.2
    change DerivedCategory.Q.map (cochainTensorMap (P.map P (𝟙 K.1.obj))
      (Q.map Q (𝟙 K.2.obj))) = _
    have h := (cochainTensorHomotopyLeft P.mapIdHomotopy (Q.map Q (𝟙 K.2.obj))).trans
      (cochainTensorHomotopyRight (𝟙 P.complex) Q.mapIdHomotopy)
    rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R) h,
      cochainTensorMap_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp {K L M} f g := by
    let P := boundedAboveChosenResolution K.1
    let P' := boundedAboveChosenResolution L.1
    let P'' := boundedAboveChosenResolution M.1
    let Q := boundedAboveChosenResolution K.2
    let Q' := boundedAboveChosenResolution L.2
    let Q'' := boundedAboveChosenResolution M.2
    change DerivedCategory.Q.map (cochainTensorMap
      (P.map P'' (f.1.hom ≫ g.1.hom)) (Q.map Q'' (f.2.hom ≫ g.2.hom))) =
      DerivedCategory.Q.map (cochainTensorMap (P.map P' f.1.hom) (Q.map Q' f.2.hom)) ≫
        DerivedCategory.Q.map (cochainTensorMap (P'.map P'' g.1.hom) (Q'.map Q'' g.2.hom))
    rw [← CategoryTheory.Functor.map_comp, cochainTensorMap_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
      ((cochainTensorHomotopyLeft (P.mapCompHomotopy P' P'' f.1.hom g.1.hom) _).trans
        (cochainTensorHomotopyRight _ (Q.mapCompHomotopy Q' Q'' f.2.hom g.2.hom)))

/-- Quasi-isomorphisms in both variables are inverted by the model functor. -/
lemma boundedAboveDerivedTensorFunctor_map_isIso
    {K L : BoundedAboveCochain (ModuleCat.{u} R) × BoundedAboveCochain (ModuleCat.{u} R)}
    (f : K ⟶ L) [QuasiIso f.1.hom] [QuasiIso f.2.hom] :
    IsIso ((boundedAboveDerivedTensorFunctor (R := R)).map f) := by
  have := (boundedAboveChosenResolution K.1).map_quasiIso
    (boundedAboveChosenResolution L.1) f.1.hom
  have := (boundedAboveChosenResolution K.2).map_quasiIso
    (boundedAboveChosenResolution L.2) f.2.hom
  have := cochainTensorMap_quasiIso_of_KProjective
    ((boundedAboveChosenResolution K.1).map (boundedAboveChosenResolution L.1) f.1.hom)
    ((boundedAboveChosenResolution K.2).map (boundedAboveChosenResolution L.2) f.2.hom)
  change IsIso (DerivedCategory.Q.map _)
  infer_instance

/-- The ordinary total tensor of the two underlying complexes. -/
def boundedAboveOrdinaryTensorFunctor :
    (BoundedAboveCochain (ModuleCat.{u} R) × BoundedAboveCochain (ModuleCat.{u} R)) ⥤
      CochainComplex (ModuleCat.{u} R) ℤ where
  obj K := cochainTensor K.1.obj K.2.obj
  map f := cochainTensorMap f.1.hom f.2.hom
  map_id K := cochainTensorMap_id K.1.obj K.2.obj
  map_comp f g := (cochainTensorMap_comp f.1.hom g.1.hom f.2.hom g.2.hom).symm

/-- The augmentation is natural in both original complexes. -/
def boundedAboveDerivedTensorAugmentation : boundedAboveDerivedTensorFunctor (R := R) ⟶
    boundedAboveOrdinaryTensorFunctor ⋙ DerivedCategory.Q where
  app K := DerivedCategory.Q.map
    ((boundedAboveChosenResolution K.1).tensorAugmentation (boundedAboveChosenResolution K.2))
  naturality {K L} f := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    change DerivedCategory.Q.map (cochainTensorMap _ _ ≫ cochainTensorMap _ _) =
      DerivedCategory.Q.map (cochainTensorMap _ _ ≫ cochainTensorMap _ _)
    rw [cochainTensorMap_comp, cochainTensorMap_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
      ((cochainTensorHomotopyLeft
        ((boundedAboveChosenResolution K.1).mapHomotopy
          (boundedAboveChosenResolution L.1) f.1.hom) _).trans
        (cochainTensorHomotopyRight _
          ((boundedAboveChosenResolution K.2).mapHomotopy
            (boundedAboveChosenResolution L.2) f.2.hom)))

end SerrePositivity
