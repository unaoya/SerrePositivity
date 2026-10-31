module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedTensorCoherenceModels
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Additivity and R-linearity of the actual derived tensor product -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Computing a tensor morphism in arbitrary projective models. -/
theorem derivedTensorHom_models {X X' Y Y' : D}
    (P : BoundedAboveDerivedModel X.obj) (P' : BoundedAboveDerivedModel X'.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (Q' : BoundedAboveDerivedModel Y'.obj)
    (f : X ⟶ X') (g : Y ⟶ Y') (h : P.complex ⟶ P'.complex) (k : Q.complex ⟶ Q'.complex)
    (hh : DerivedCategory.Q.map h ≫ P'.iso.hom = P.iso.hom ≫ f.hom)
    (hk : DerivedCategory.Q.map k ≫ Q'.iso.hom = Q.iso.hom ≫ g.hom) :
    (f ⊗ₘ g).hom = (boundedAboveDerivedTensorModelIso X Y P Q).hom ≫
      DerivedCategory.Q.map (cochainTensorMap h k) ≫
        (boundedAboveDerivedTensorModelIso X' Y' P' Q').inv := by
  apply (cancel_mono (boundedAboveDerivedTensorModelIso X' Y' P' Q').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact boundedAboveDerivedTensorModelIso_naturality P P' Q Q' f g h k hh hk

/-- The actual derived tensor is additive in its first morphism. -/
theorem derivedTensorHom_add_left {X X' Y Y' : D} (f f' : X ⟶ X') (g : Y ⟶ Y') :
    (f + f') ⊗ₘ g = f ⊗ₘ g + f' ⊗ₘ g := by
  let P := boundedAboveDerivedChosenModel X
  let P' := boundedAboveDerivedChosenModel X'
  let Q := boundedAboveDerivedChosenModel Y
  let Q' := boundedAboveDerivedChosenModel Y'
  let h := P.map P' f.hom
  let h' := P.map P' f'.hom
  let k := Q.map Q' g.hom
  have hs : DerivedCategory.Q.map (h + h') ≫ P'.iso.hom = P.iso.hom ≫ (f + f').hom := by
    change DerivedCategory.Q.map (h + h') ≫ P'.iso.hom = P.iso.hom ≫ (f.hom + f'.hom)
    dsimp only [h, h']
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, P.map_naturality]
  apply InducedCategory.hom_ext
  change ((f + f') ⊗ₘ g).hom = (f ⊗ₘ g).hom + (f' ⊗ₘ g).hom
  rw [derivedTensorHom_models P P' Q Q' (f + f') g (h + h') k hs (Q.map_naturality Q' g.hom),
    derivedTensorHom_models P P' Q Q' f g h k (P.map_naturality P' f.hom)
      (Q.map_naturality Q' g.hom),
    derivedTensorHom_models P P' Q Q' f' g h' k (P.map_naturality P' f'.hom)
      (Q.map_naturality Q' g.hom),
    cochainTensorMap_add_left, Functor.map_add]
  simp only [Preadditive.add_comp, Preadditive.comp_add]

/-- The actual derived tensor is additive in its second morphism. -/
theorem derivedTensorHom_add_right {X X' Y Y' : D} (f : X ⟶ X') (g g' : Y ⟶ Y') :
    f ⊗ₘ (g + g') = f ⊗ₘ g + f ⊗ₘ g' := by
  let P := boundedAboveDerivedChosenModel X
  let P' := boundedAboveDerivedChosenModel X'
  let Q := boundedAboveDerivedChosenModel Y
  let Q' := boundedAboveDerivedChosenModel Y'
  let h := P.map P' f.hom
  let k := Q.map Q' g.hom
  let k' := Q.map Q' g'.hom
  have hs : DerivedCategory.Q.map (k + k') ≫ Q'.iso.hom = Q.iso.hom ≫ (g + g').hom := by
    change DerivedCategory.Q.map (k + k') ≫ Q'.iso.hom = Q.iso.hom ≫ (g.hom + g'.hom)
    dsimp only [k, k']
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, Q.map_naturality]
  apply InducedCategory.hom_ext
  change (f ⊗ₘ (g + g')).hom = (f ⊗ₘ g).hom + (f ⊗ₘ g').hom
  rw [derivedTensorHom_models P P' Q Q' f (g + g') h (k + k')
      (P.map_naturality P' f.hom) hs,
    derivedTensorHom_models P P' Q Q' f g h k (P.map_naturality P' f.hom)
      (Q.map_naturality Q' g.hom),
    derivedTensorHom_models P P' Q Q' f g' h k' (P.map_naturality P' f.hom)
      (Q.map_naturality Q' g'.hom),
    cochainTensorMap_add_right, Functor.map_add]
  simp only [Preadditive.add_comp, Preadditive.comp_add]

instance boundedAboveDerivedTensorLeft_additive (X : D) : (tensorLeft X).Additive where
  map_add := derivedTensorHom_add_right (𝟙 X) _ _

instance boundedAboveDerivedTensorRight_additive (X : D) : (tensorRight X).Additive where
  map_add := derivedTensorHom_add_left _ _ (𝟙 X)

/-- The actual monoidal structure is preadditive, using the existing addition on derived maps. -/
instance boundedAboveDerivedMonoidalPreadditive : MonoidalPreadditive D where
  whiskerLeft_zero {X Y Z} := by
    change (tensorLeft X).map (0 : Y ⟶ Z) = 0
    exact (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := by
    change (tensorRight X).map (0 : Y ⟶ Z) = 0
    exact (tensorRight X).map_zero Y Z
  whiskerLeft_add f g := derivedTensorHom_add_right _ f g
  add_whiskerRight f g := derivedTensorHom_add_left f g _

/-- The actual tensor uses the existing R-scalar multiplication in its first argument. -/
theorem derivedTensorHom_smul_left {X X' Y Y' : D} (r : R) (f : X ⟶ X') (g : Y ⟶ Y') :
    (r • f) ⊗ₘ g = r • (f ⊗ₘ g) := by
  let P := boundedAboveDerivedChosenModel X
  let P' := boundedAboveDerivedChosenModel X'
  let Q := boundedAboveDerivedChosenModel Y
  let Q' := boundedAboveDerivedChosenModel Y'
  let h := P.map P' f.hom
  let k := Q.map Q' g.hom
  have hs : DerivedCategory.Q.map (r • h) ≫ P'.iso.hom = P.iso.hom ≫ (r • f).hom := by
    change DerivedCategory.Q.map (r • h) ≫ P'.iso.hom = P.iso.hom ≫ (r • f.hom)
    dsimp only [h]
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, P.map_naturality]
  apply InducedCategory.hom_ext
  change ((r • f) ⊗ₘ g).hom = r • (f ⊗ₘ g).hom
  rw [derivedTensorHom_models P P' Q Q' (r • f) g (r • h) k hs (Q.map_naturality Q' g.hom),
    derivedTensorHom_models P P' Q Q' f g h k (P.map_naturality P' f.hom)
      (Q.map_naturality Q' g.hom), cochainTensorMap_smul_left, Functor.map_smul]
  simp only [Linear.smul_comp, Linear.comp_smul]

/-- The actual tensor uses the existing R-scalar multiplication in its second argument. -/
theorem derivedTensorHom_smul_right {X X' Y Y' : D} (r : R) (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ (r • g) = r • (f ⊗ₘ g) := by
  let P := boundedAboveDerivedChosenModel X
  let P' := boundedAboveDerivedChosenModel X'
  let Q := boundedAboveDerivedChosenModel Y
  let Q' := boundedAboveDerivedChosenModel Y'
  let h := P.map P' f.hom
  let k := Q.map Q' g.hom
  have hs : DerivedCategory.Q.map (r • k) ≫ Q'.iso.hom = Q.iso.hom ≫ (r • g).hom := by
    change DerivedCategory.Q.map (r • k) ≫ Q'.iso.hom = Q.iso.hom ≫ (r • g.hom)
    dsimp only [k]
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, Q.map_naturality]
  apply InducedCategory.hom_ext
  change (f ⊗ₘ (r • g)).hom = r • (f ⊗ₘ g).hom
  rw [derivedTensorHom_models P P' Q Q' f (r • g) h (r • k)
      (P.map_naturality P' f.hom) hs,
    derivedTensorHom_models P P' Q Q' f g h k (P.map_naturality P' f.hom)
      (Q.map_naturality Q' g.hom), cochainTensorMap_smul_right, Functor.map_smul]
  simp only [Linear.smul_comp, Linear.comp_smul]

/-- The actual derived monoidal category is linear over its original coefficient ring. -/
instance boundedAboveDerivedMonoidalLinear : MonoidalLinear R D where
  whiskerLeft_smul X {_ _} r f := derivedTensorHom_smul_right r (𝟙 X) f
  smul_whiskerRight r {_ _} f X := derivedTensorHom_smul_left r f (𝟙 X)

end SerrePositivity
