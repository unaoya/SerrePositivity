module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOne
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBinaryCoproduct
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

/-! # The good cylinder carried by a cosimplicial resolution

The actual interval boundary is the coproduct of its two vertices. Finite
tensor preservation identifies the Reedy boundary cofibration with the
coproduct of the two cofaces. The code uses only finite colimits.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)

abbrev vertexTensorIso :=
  FiniteTensor.representationIso A (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) (Iso.refl _)

abbrev boundaryOneCofan : BinaryCofan (A.obj (SimplexCategory.mk 0))
    (A.obj (SimplexCategory.mk 0)) :=
  BinaryCofan.mk
    ((vertexTensorIso A).inv ≫ FiniteTensor.map A (SSet.boundary.ι.{v} (1 : Fin 2)))
    ((vertexTensorIso A).inv ≫ FiniteTensor.map A (SSet.boundary.ι.{v} (0 : Fin 2)))

def boundaryOneCofanIsColimit : IsColimit (boundaryOneCofan A) := by
  have h := FiniteTensor.isColimitBinaryCoproduct A BoundaryOne.isColimit.{v}
  exact BinaryCofan.isColimitCompRightIso _ (vertexTensorIso A).inv
    (BinaryCofan.isColimitCompLeftIso _ (vertexTensorIso A).inv h)

abbrev boundaryOneCoproductIso :
    A.obj (SimplexCategory.mk 0) ⨿ A.obj (SimplexCategory.mk 0) ≅
      SubcomplexTensor.obj (SSet.boundary.{v} 1) A :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (boundaryOneCofanIsColimit A)

lemma boundaryOneCofan_inl_inclusion : (boundaryOneCofan A).inl ≫
    SubcomplexTensor.inclusion (SSet.boundary.{v} 1) A = A.map (SimplexCategory.δ (1 : Fin 2)) := by
  have hi := finiteTensor_map_ι A (SSet.boundary.{v} 1)
  have hn := FiniteTensor.standard_naturality A (SimplexCategory.δ (1 : Fin 2))
  have hm := FiniteTensor.map_comp A (SSet.boundary.ι.{v} (1 : Fin 2)) (SSet.boundary 1).ι
  change ((vertexTensorIso A).inv ≫ FiniteTensor.map A (SSet.boundary.ι (1 : Fin 2))) ≫
    SubcomplexTensor.inclusion (SSet.boundary 1) A = _
  rw [Category.assoc, ← hi,
    ← Category.assoc (FiniteTensor.map A (SSet.boundary.ι (1 : Fin 2)))
      (FiniteTensor.map A (SSet.boundary 1).ι), hm,
    SSet.boundary.ι_ι]
  exact (congrArg (fun f ↦ (vertexTensorIso A).inv ≫ f) hn).trans
    (Iso.inv_hom_id_assoc (vertexTensorIso A) _)

lemma boundaryOneCofan_inr_inclusion : (boundaryOneCofan A).inr ≫
    SubcomplexTensor.inclusion (SSet.boundary.{v} 1) A = A.map (SimplexCategory.δ (0 : Fin 2)) := by
  have hi := finiteTensor_map_ι A (SSet.boundary.{v} 1)
  have hn := FiniteTensor.standard_naturality A (SimplexCategory.δ (0 : Fin 2))
  have hm := FiniteTensor.map_comp A (SSet.boundary.ι.{v} (0 : Fin 2)) (SSet.boundary 1).ι
  change ((vertexTensorIso A).inv ≫ FiniteTensor.map A (SSet.boundary.ι (0 : Fin 2))) ≫
    SubcomplexTensor.inclusion (SSet.boundary 1) A = _
  rw [Category.assoc, ← hi,
    ← Category.assoc (FiniteTensor.map A (SSet.boundary.ι (0 : Fin 2)))
      (FiniteTensor.map A (SSet.boundary 1).ι), hm,
    SSet.boundary.ι_ι]
  exact (congrArg (fun f ↦ (vertexTensorIso A).inv ≫ f) hn).trans
    (Iso.inv_hom_id_assoc (vertexTensorIso A) _)

lemma boundaryOneCoproductIso_inclusion : (boundaryOneCoproductIso A).hom ≫
    SubcomplexTensor.inclusion (SSet.boundary.{v} 1) A =
      coprod.desc (A.map (SimplexCategory.δ (1 : Fin 2)))
        (A.map (SimplexCategory.δ (0 : Fin 2))) := by
  apply coprod.hom_ext
  · rw [← Category.assoc]
    have h := (coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
      (boundaryOneCofanIsColimit A) (Discrete.mk WalkingPair.left)
    exact (congrArg (fun f ↦ f ≫ SubcomplexTensor.inclusion (SSet.boundary.{v} 1) A) h).trans
      ((boundaryOneCofan_inl_inclusion A).trans (coprod.inl_desc _ _).symm)
  · rw [← Category.assoc]
    have h := (coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
      (boundaryOneCofanIsColimit A) (Discrete.mk WalkingPair.right)
    exact (congrArg (fun f ↦ f ≫ SubcomplexTensor.inclusion (SSet.boundary.{v} 1) A) h).trans
      ((boundaryOneCofan_inr_inclusion A).trans (coprod.inr_desc _ _).symm)

def cosimplicialCylinder [CategoryWithWeakEquivalences C]
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    Cylinder (A.obj (SimplexCategory.mk 0)) where
  I := A.obj (SimplexCategory.mk 1)
  i₀ := A.map (SimplexCategory.δ (1 : Fin 2))
  i₁ := A.map (SimplexCategory.δ (0 : Fin 2))
  π := A.map (SimplexCategory.σ (0 : Fin 1))
  i₀_π := (A.map_comp _ _).symm.trans
    ((congrArg A.map (SimplexCategory.δ_comp_σ_succ (i := (0 : Fin 1)))).trans (A.map_id _))
  i₁_π := (A.map_comp _ _).symm.trans
    ((congrArg A.map (SimplexCategory.δ_comp_σ_self (i := (0 : Fin 1)))).trans (A.map_id _))
  weakEquivalence_π := ⟨hconst _⟩

lemma cosimplicialCylinder_isGood [ModelCategory C]
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f)) :
    (cosimplicialCylinder A hconst).IsGood := by
  have h := (cofibrations C).comp_mem _ _
    ((cofibrations C).of_isIso (boundaryOneCoproductIso A).hom)
    (boundaryTensor_cofibration A 1 hA)
  have hc : cofibrations C (coprod.desc (A.map (SimplexCategory.δ (1 : Fin 2)))
      (A.map (SimplexCategory.δ (0 : Fin 2)))) :=
    (boundaryOneCoproductIso_inclusion A) ▸ h
  exact ⟨⟨hc⟩⟩

end SerrePositivity.HomotopyFunctionComplex
