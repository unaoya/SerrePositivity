module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftFillers
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! # Actual universe comparison for whole tensor and standard-simplex families -/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLift

/-- The actual degreewise product comparison, independent of model structures. -/
def tensorIso (K T : SSet.{v}) : obj.{w} (K ⊗ T) ≅ obj.{w} K ⊗ obj.{w} T :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => (ULift.up x.down.1, ULift.up x.down.2)
      invFun := fun x => ULift.up (x.1.down, x.2.down)
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro m n f; ext x; rfl)

variable {K T P : SSet.{v}}

def tensorMap (h : K ⊗ T ⟶ P) : obj.{w} K ⊗ obj.{w} T ⟶ obj.{w} P :=
  (tensorIso K T).inv ≫ map h

def lowerTensor (h : obj.{w} K ⊗ obj.{w} T ⟶ obj.{w} P) : K ⊗ T ⟶ P :=
  lower ((tensorIso K T).hom ≫ h)

lemma tensorMap_lowerTensor (h : obj.{w} K ⊗ obj.{w} T ⟶ obj.{w} P) :
    tensorMap (lowerTensor h) = h := by
  rw [tensorMap, lowerTensor, map_lower, Iso.inv_hom_id_assoc]

lemma lowerTensor_tensorMap (h : K ⊗ T ⟶ P) : lowerTensor (tensorMap.{w} h) = h := by
  rw [lowerTensor, tensorMap, Iso.hom_inv_id_assoc, lower_map]

/-- Lift the entire original family to the actual larger standard simplex. -/
def simplexTensorMap {n : ℕ} (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk n) ⟶ obj.{w} P :=
  obj K ◁ (stdIso n).inv ≫ tensorMap h

def lowerSimplexTensor {n : ℕ}
    (h : obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk n) ⟶ obj.{w} P) :
      K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P :=
  lowerTensor (obj K ◁ (stdIso n).hom ≫ h)

lemma lowerSimplexTensor_simplexTensorMap {n : ℕ}
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    lowerSimplexTensor (simplexTensorMap.{w} h) = h := by
  rw [lowerSimplexTensor, simplexTensorMap, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp, lowerTensor_tensorMap]

lemma simplexTensorMap_lowerSimplexTensor {n : ℕ}
    (h : obj.{w} K ⊗ SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk n) ⟶ obj.{w} P) :
    simplexTensorMap (lowerSimplexTensor h) = h := by
  rw [simplexTensorMap, lowerSimplexTensor, tensorMap_lowerTensor, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

lemma simplexTensorMap_operator {n m : ℕ}
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    obj.{w} K ◁ SSet.stdSimplex.map θ ≫ simplexTensorMap h =
      simplexTensorMap ((K ◁ SSet.stdSimplex.map θ) ≫ h) := by
  ext d x
  rfl

lemma simplexTensorMap_source {V : SSet.{v}} (i : V ⟶ K) {n : ℕ}
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) :
    map.{w} i ▷ SSet.stdSimplex.obj (SimplexCategory.mk n) ≫ simplexTensorMap h =
      simplexTensorMap ((i ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ h) := by
  ext d x
  rfl

lemma simplexTensorMap_target {Q : SSet.{v}} {n : ℕ}
    (h : K ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ P) (q : P ⟶ Q) :
    simplexTensorMap.{w} h ≫ map q = simplexTensorMap (h ≫ q) := by
  ext d x
  rfl

lemma simplexTensorMap_constant (b : K ⟶ P) (n : ℕ) :
    simplexTensorMap.{w} (fst K (SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ b) =
      fst (obj.{w} K) (SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ map b := by
  ext d x
  rfl

end SerrePositivity.SimplicialModel.UniverseLift
