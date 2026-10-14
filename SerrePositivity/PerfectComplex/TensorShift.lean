module
public import SerrePositivity.PerfectComplex.TensorSupport
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Shifts and additivity of the standard tensor complex

The left shift comparison has no sign; the right one carries the sign
`(-1)^(i*s)` on a tensor whose left degree is `i`. Both comparisons are
natural chain isomorphisms, with the coherence of shifts inherited from
Mathlib's totalization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Shift the left factor of the tensor complex. -/
abbrev cochainTensorShiftLeft (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℤ) :
    cochainTensor (P⟦s⟧) Q ≅ (cochainTensor P Q)⟦s⟧ :=
  CochainComplex.mapBifunctorShift₁Iso P Q (curriedTensor (ModuleCat.{u} R)) s

/-- Shift the right factor, including its totalization sign. -/
abbrev cochainTensorShiftRight (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℤ) :
    cochainTensor P (Q⟦s⟧) ≅ (cochainTensor P Q)⟦s⟧ :=
  CochainComplex.mapBifunctorShift₂Iso P Q (curriedTensor (ModuleCat.{u} R)) s

@[reassoc]
lemma cochainTensorShiftLeft_naturality {P P' Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (s : ℤ) :
    cochainTensorMap (f⟦s⟧') (𝟙 Q) ≫ (cochainTensorShiftLeft P' Q s).hom =
      (cochainTensorShiftLeft P Q s).hom ≫ (cochainTensorMap f (𝟙 Q))⟦s⟧' :=
  CochainComplex.mapBifunctorShift₁Iso_hom_naturality₁ f Q
    (curriedTensor (ModuleCat.{u} R)) s

@[reassoc]
lemma cochainTensorShiftRight_naturality {P Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : Q ⟶ Q') (s : ℤ) :
    cochainTensorMap (𝟙 P) (g⟦s⟧') ≫ (cochainTensorShiftRight P Q' s).hom =
      (cochainTensorShiftRight P Q s).hom ≫ (cochainTensorMap (𝟙 P) g)⟦s⟧' :=
  CochainComplex.mapBifunctorShift₂Iso_hom_naturality₂ P g
    (curriedTensor (ModuleCat.{u} R)) s

/-- Homogeneous formula for the sign-free left shift comparison. -/
@[reassoc]
lemma ιTensorObj_cochainTensorShiftLeft (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (s i j n : ℤ) (h : i + j = n) :
    ιTensorObj (P⟦s⟧) Q i j n h ≫ (cochainTensorShiftLeft P Q s).hom.f n =
      ((CochainComplex.shiftFunctorObjXIso P s i (i + s) rfl).hom ▷ Q.X j) ≫
        ιTensorObj P Q (i + s) j (n + s) (by omega) ≫
          (CochainComplex.shiftFunctorObjXIso (cochainTensor P Q) s n (n + s) rfl).inv :=
  CochainComplex.ι_mapBifunctorShift₁Iso_hom_f P Q (curriedTensor (ModuleCat.{u} R))
    s i j n h (i + s) (n + s) rfl rfl

/-- Homogeneous formula for the sign in the right shift comparison. -/
@[reassoc]
lemma ιTensorObj_cochainTensorShiftRight (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (s i j n : ℤ) (h : i + j = n) :
    ιTensorObj P (Q⟦s⟧) i j n h ≫ (cochainTensorShiftRight P Q s).hom.f n =
      (i * s).negOnePow •
        (P.X i ◁ (CochainComplex.shiftFunctorObjXIso Q s j (j + s) rfl).hom) ≫
          ιTensorObj P Q i (j + s) (n + s) (by omega) ≫
            (CochainComplex.shiftFunctorObjXIso (cochainTensor P Q) s n (n + s) rfl).inv :=
  CochainComplex.ι_mapBifunctorShift₂Iso_hom_f P Q (curriedTensor (ModuleCat.{u} R))
    s i j n h (j + s) (n + s) rfl rfl

lemma cochainTensorMap_add_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f f' : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap (f + f') g = cochainTensorMap f g + cochainTensorMap f' g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.add_f_apply, Preadditive.comp_add]
  rw [ι_mapBifunctorMap, ι_mapBifunctorMap, ι_mapBifunctorMap]
  simp [Preadditive.add_comp]

lemma cochainTensorMap_add_right {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g g' : Q ⟶ Q') :
    cochainTensorMap f (g + g') = cochainTensorMap f g + cochainTensorMap f g' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.add_f_apply, Preadditive.comp_add]
  rw [ι_mapBifunctorMap, ι_mapBifunctorMap, ι_mapBifunctorMap]
  simp [Preadditive.comp_add, Preadditive.add_comp]

/-- The functor of tensoring on the right with a fixed complex. -/
abbrev cochainTensorFixedRight (Q : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.flip.obj Q

/-- The functor of tensoring on the left with a fixed complex. -/
abbrev cochainTensorFixedLeft (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex.obj P

instance (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorFixedRight Q).Additive where
  map_add := cochainTensorMap_add_left _ _ (𝟙 Q)

instance (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorFixedLeft P).Additive where
  map_add := cochainTensorMap_add_right (𝟙 P) _ _

/-- Tensoring on the right commutes with all integer shifts coherently. -/
abbrev cochainTensorFixedRight_commShift (Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorFixedRight Q).CommShift ℤ := inferInstance

/-- Tensoring on the left commutes with all integer shifts coherently. -/
abbrev cochainTensorFixedLeft_commShift (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainTensorFixedLeft P).CommShift ℤ := inferInstance
end SerrePositivity
