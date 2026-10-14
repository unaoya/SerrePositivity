module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModels
public import SerrePositivity.HomologicalAlgebra.BoundedAboveTensorFunctor

/-! # Tensor product on the actual bounded-above derived category -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Upper bounds add under tensor totalization, without any lower bounds. -/
lemma cochainTensor_isStrictlyLE
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyLE a] [Q.IsStrictlyLE b] : (cochainTensor P Q).IsStrictlyLE (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have hs (ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n}) :
      IsZero (cochainTensorSummand P Q n ij) := by
    by_cases hi : a < ij.val.1
    · exact cochainTensorSummand_isZero_left P Q n ij (P.isZero_of_isStrictlyLE a _ hi)
    · exact cochainTensorSummand_isZero_right P Q n ij
        (Q.isZero_of_isStrictlyLE b _ (by have := ij.property; omega))
  have hz : IsZero (∐ cochainTensorSummand P Q n : ModuleCat.{u} R) := by
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro ij
    exact (hs ij).eq_of_src _ _
  exact hz.of_iso (cochainTensorXIso P Q n).symm

/-- Derived tensor is a bifunctor on Mathlib's bounded-above derived category.
Its values stay bounded above; arbitrary negative tails are allowed. -/
def boundedAboveDerivedTensor :
    (DerivedCategory.Minus (ModuleCat.{u} R) × DerivedCategory.Minus (ModuleCat.{u} R)) ⥤
      DerivedCategory.Minus (ModuleCat.{u} R) where
  obj X := by
    let P := boundedAboveDerivedChosenModel X.1
    let Q := boundedAboveDerivedChosenModel X.2
    have := cochainTensor_isStrictlyLE P.complex Q.complex P.bound Q.bound
    exact ⟨DerivedCategory.Q.obj (cochainTensor P.complex Q.complex),
      ⟨P.bound + Q.bound, inferInstance⟩⟩
  map {X Y} f := ObjectProperty.homMk (DerivedCategory.Q.map (cochainTensorMap
    ((boundedAboveDerivedChosenModel X.1).map (boundedAboveDerivedChosenModel Y.1) f.1.hom)
    ((boundedAboveDerivedChosenModel X.2).map (boundedAboveDerivedChosenModel Y.2) f.2.hom)))
  map_id X := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X.1
    let Q := boundedAboveDerivedChosenModel X.2
    change DerivedCategory.Q.map (cochainTensorMap (P.map P (𝟙 X.1.obj))
      (Q.map Q (𝟙 X.2.obj))) = _
    have h := (cochainTensorHomotopyLeft P.mapIdHomotopy (Q.map Q (𝟙 X.2.obj))).trans
      (cochainTensorHomotopyRight (𝟙 P.complex) Q.mapIdHomotopy)
    rw [DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R) h,
      cochainTensorMap_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X.1
    let P' := boundedAboveDerivedChosenModel Y.1
    let P'' := boundedAboveDerivedChosenModel Z.1
    let Q := boundedAboveDerivedChosenModel X.2
    let Q' := boundedAboveDerivedChosenModel Y.2
    let Q'' := boundedAboveDerivedChosenModel Z.2
    change DerivedCategory.Q.map (cochainTensorMap
      (P.map P'' (f.1.hom ≫ g.1.hom)) (Q.map Q'' (f.2.hom ≫ g.2.hom))) =
      DerivedCategory.Q.map (cochainTensorMap (P.map P' f.1.hom) (Q.map Q' f.2.hom)) ≫
        DerivedCategory.Q.map (cochainTensorMap (P'.map P'' g.1.hom) (Q'.map Q'' g.2.hom))
    rw [← CategoryTheory.Functor.map_comp, cochainTensorMap_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
      ((cochainTensorHomotopyLeft (P.mapCompHomotopy P' P'' f.1.hom g.1.hom) _).trans
        (cochainTensorHomotopyRight _ (Q.mapCompHomotopy Q' Q'' f.2.hom g.2.hom)))

/-- Compute the derived tensor using any specified bounded-above projective models. -/
def boundedAboveDerivedTensorModelIso
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R))
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y.obj) :
    ((boundedAboveDerivedTensor.obj (X, Y)).obj) ≅
      DerivedCategory.Q.obj (cochainTensor P.complex Q.complex) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel Y
  have := A.map_quasiIso P (𝟙 X.obj)
  have := B.map_quasiIso Q (𝟙 Y.obj)
  have := cochainTensorMap_quasiIso_of_KProjective (A.map P (𝟙 X.obj)) (B.map Q (𝟙 Y.obj))
  exact asIso (DerivedCategory.Q.map (cochainTensorMap (A.map P (𝟙 X.obj)) (B.map Q (𝟙 Y.obj))))

/-- The derived-object functor recovers the earlier complex-model functor naturally. -/
def boundedAboveDerivedTensorComplexComparison :
    (boundedAboveDerivedQ.prod boundedAboveDerivedQ) ⋙ boundedAboveDerivedTensor ⋙
        DerivedCategory.Minus.ι ≅ boundedAboveDerivedTensorFunctor (R := R) := by
  refine NatIso.ofComponents (fun K => boundedAboveDerivedTensorModelIso
    (boundedAboveDerivedQ.obj K.1) (boundedAboveDerivedQ.obj K.2)
    (BoundedAboveDerivedModel.ofResolution (boundedAboveChosenResolution K.1))
    (BoundedAboveDerivedModel.ofResolution (boundedAboveChosenResolution K.2))) ?_
  intro K L f
  let A := boundedAboveDerivedChosenModel (boundedAboveDerivedQ.obj K.1)
  let B := boundedAboveDerivedChosenModel (boundedAboveDerivedQ.obj L.1)
  let C := boundedAboveDerivedChosenModel (boundedAboveDerivedQ.obj K.2)
  let D := boundedAboveDerivedChosenModel (boundedAboveDerivedQ.obj L.2)
  let P := boundedAboveChosenResolution K.1
  let P' := boundedAboveChosenResolution L.1
  let Q := boundedAboveChosenResolution K.2
  let Q' := boundedAboveChosenResolution L.2
  let p := BoundedAboveDerivedModel.ofResolution P
  let p' := BoundedAboveDerivedModel.ofResolution P'
  let q := BoundedAboveDerivedModel.ofResolution Q
  let q' := BoundedAboveDerivedModel.ofResolution Q'
  have h₁ := (A.mapSquareHomotopy p B p' (DerivedCategory.Q.map f.1.hom)).trans
    ((BoundedAboveDerivedModel.ofResolutionMapHomotopy P P' f.1.hom).compLeft
      (A.map p (𝟙 _)))
  have h₂ := (C.mapSquareHomotopy q D q' (DerivedCategory.Q.map f.2.hom)).trans
    ((BoundedAboveDerivedModel.ofResolutionMapHomotopy Q Q' f.2.hom).compLeft
      (C.map q (𝟙 _)))
  change DerivedCategory.Q.map (cochainTensorMap
      (A.map B (DerivedCategory.Q.map f.1.hom))
      (C.map D (DerivedCategory.Q.map f.2.hom))) ≫
      DerivedCategory.Q.map (cochainTensorMap (B.map p' (𝟙 _)) (D.map q' (𝟙 _))) =
    DerivedCategory.Q.map (cochainTensorMap (A.map p (𝟙 _)) (C.map q (𝟙 _))) ≫
      DerivedCategory.Q.map (cochainTensorMap (P.map P' f.1.hom) (Q.map Q' f.2.hom))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cochainTensorMap_comp, cochainTensorMap_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
    ((cochainTensorHomotopyLeft h₁ _).trans (cochainTensorHomotopyRight _ h₂))

/-- Model computation respects arbitrary chain representatives of the two derived morphisms. -/
lemma boundedAboveDerivedTensorModelIso_naturality
    {X X' Y Y' : DerivedCategory.Minus (ModuleCat.{u} R)}
    (P : BoundedAboveDerivedModel X.obj) (P' : BoundedAboveDerivedModel X'.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (Q' : BoundedAboveDerivedModel Y'.obj)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : P.complex ⟶ P'.complex) (k : Q.complex ⟶ Q'.complex)
    (hh : DerivedCategory.Q.map h ≫ P'.iso.hom = P.iso.hom ≫ f.hom)
    (hk : DerivedCategory.Q.map k ≫ Q'.iso.hom = Q.iso.hom ≫ g.hom) :
    (boundedAboveDerivedTensor.map (f, g)).hom ≫
        (boundedAboveDerivedTensorModelIso X' Y' P' Q').hom =
      (boundedAboveDerivedTensorModelIso X Y P Q).hom ≫
        DerivedCategory.Q.map (cochainTensorMap h k) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel X'
  let C := boundedAboveDerivedChosenModel Y
  let D := boundedAboveDerivedChosenModel Y'
  have h₁ := (A.mapSquareHomotopy P B P' f.hom).trans
    ((P.mapHomotopyOfNaturality P' f.hom h hh).compLeft (A.map P (𝟙 _)))
  have h₂ := (C.mapSquareHomotopy Q D Q' g.hom).trans
    ((Q.mapHomotopyOfNaturality Q' g.hom k hk).compLeft (C.map Q (𝟙 _)))
  change DerivedCategory.Q.map (cochainTensorMap (A.map B f.hom) (C.map D g.hom)) ≫
      DerivedCategory.Q.map (cochainTensorMap (B.map P' (𝟙 _)) (D.map Q' (𝟙 _))) =
    DerivedCategory.Q.map (cochainTensorMap (A.map P (𝟙 _)) (C.map Q (𝟙 _))) ≫
      DerivedCategory.Q.map (cochainTensorMap h k)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cochainTensorMap_comp, cochainTensorMap_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R)
    ((cochainTensorHomotopyLeft h₁ _).trans (cochainTensorHomotopyRight _ h₂))

end SerrePositivity
