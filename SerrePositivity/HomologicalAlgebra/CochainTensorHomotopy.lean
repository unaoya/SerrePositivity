module
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
public import SerrePositivity.HomologicalAlgebra.CochainTensorSymmetry
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-! # Tensor products preserve homotopies and scalar null homotopies -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Tensoring a homotopy in the left variable with a fixed chain map. -/
def cochainTensorHomotopyLeft {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    {f f' : P ⟶ P'} (h : Homotopy f f') (g : Q ⟶ Q') :
    Homotopy (cochainTensorMap f g) (cochainTensorMap f' g) :=
  mapBifunctorMapHomotopy₁ h g (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

/-- Tensoring a homotopy in the right variable with a fixed chain map. -/
def cochainTensorHomotopyRight {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') {g g' : Q ⟶ Q'} (h : Homotopy g g') :
    Homotopy (cochainTensorMap f g) (cochainTensorMap f g') :=
  mapBifunctorMapHomotopy₂ f h (curriedTensor (ModuleCat.{u} R)) (.up ℤ)

@[simp] lemma cochainTensorMap_id (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap (𝟙 P) (𝟙 Q) = 𝟙 (cochainTensor P Q) := by
  change (𝟙 P) ⊗ₘ (𝟙 Q) = _
  simp
  rfl

lemma cochainTensorMap_comp {P P' P'' Q Q' Q'' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    cochainTensorMap f g ≫ cochainTensorMap f' g' = cochainTensorMap (f ≫ f') (g ≫ g') := by
  change (f ⊗ₘ g) ≫ (f' ⊗ₘ g') = _
  exact tensorHom_comp_tensorHom _ _ _ _

/-- Homotopy equivalences in both factors give a homotopy equivalence of tensor complexes. -/
def cochainTensorHomotopyEquiv {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv P P') (f : HomotopyEquiv Q Q') :
    HomotopyEquiv (cochainTensor P Q) (cochainTensor P' Q') where
  hom := cochainTensorMap e.hom f.hom
  inv := cochainTensorMap e.inv f.inv
  homotopyHomInvId := by
    rw [cochainTensorMap_comp, ← cochainTensorMap_id]
    exact (cochainTensorHomotopyLeft e.homotopyHomInvId _).trans
      (cochainTensorHomotopyRight _ f.homotopyHomInvId)
  homotopyInvHomId := by
    rw [cochainTensorMap_comp, ← cochainTensorMap_id]
    exact (cochainTensorHomotopyLeft e.homotopyInvHomId _).trans
      (cochainTensorHomotopyRight _ f.homotopyInvHomId)

lemma cochainTensorMap_smul_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (r : R) (f : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap (r • f) g = r • cochainTensorMap f g := by
  change (r • f) ⊗ₘ g = r • (f ⊗ₘ g)
  simp [tensorHom_def, Linear.smul_comp]

@[simp] lemma cochainTensorMap_zero_left {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : Q ⟶ Q') : cochainTensorMap (0 : P ⟶ P') g = 0 := by
  exact MonoidalPreadditive.zero_tensor g

end SerrePositivity
