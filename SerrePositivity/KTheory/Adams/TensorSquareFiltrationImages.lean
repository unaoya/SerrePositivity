module

public import SerrePositivity.KTheory.Adams.TensorSquareMixedSplitting

/-! # The kernel model agrees with the tensor image filtration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))

def tensorSquareKernelPartialLeft : cochainTensor S.X₁ S.X₂ ⟶ tensorSquareKernel S.g :=
  kernel.lift (tensorSquareMap S.g) (cochainTensorMap S.f (𝟙 S.X₂)) (by
    rw [cochainTensorMap_comp, S.zero, id_comp, cochainTensorMap_zero_left])

def tensorSquareKernelPartialRight : cochainTensor S.X₂ S.X₁ ⟶ tensorSquareKernel S.g :=
  kernel.lift (tensorSquareMap S.g) (cochainTensorMap (𝟙 S.X₂) S.f) (by
    rw [cochainTensorMap_comp, id_comp, S.zero, cochainTensorMap_zero_right])

@[simp, reassoc]
lemma tensorSquareKernelPartialLeft_inclusion :
    tensorSquareKernelPartialLeft S ≫ tensorSquareKernelInclusion S.g =
      cochainTensorMap S.f (𝟙 S.X₂) := kernel.lift_ι _ _ _

@[simp, reassoc]
lemma tensorSquareKernelPartialRight_inclusion :
    tensorSquareKernelPartialRight S ≫ tensorSquareKernelInclusion S.g =
      cochainTensorMap (𝟙 S.X₂) S.f := kernel.lift_ι _ _ _

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))
  (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorSquareKernelInclusion_decomposition (n : ℤ) :
    (tensorSquareKernelInclusion S.g).f n =
      tensorSquareMixedRetractionX S σ n ≫ (tensorSquareMap S.f).f n +
      (tensorSquareMixedLeft S hS hproj).f n ≫
        cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n +
      (tensorSquareMixedRight S hS hproj).f n ≫
        cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n := by
  calc
    _ = (tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n +
        (tensorSquareMixedLeft S hS hproj).f n ≫ tensorSquareMixedSectionLeftX S hS hproj σ n +
        (tensorSquareMixedRight S hS hproj).f n ≫ tensorSquareMixedSectionRightX S hS hproj σ n) ≫
        (tensorSquareKernelInclusion S.g).f n := by rw [tensorSquareMixedSplitting_total, id_comp]
    _ = _ := by
      rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc,
        ← HomologicalComplex.comp_f, tensorSquareKernelFirstMap_inclusion,
        tensorSquareMixedSectionLeftX_inclusion, tensorSquareMixedSectionRightX_inclusion]

include hS hproj σ in
/-- In each degree, the intermediate layer is precisely the sum of the two partial tensor images. -/
lemma tensorSquareKernelInclusion_range (n : ℤ) :
    LinearMap.range ((tensorSquareKernelInclusion S.g).f n).hom =
      LinearMap.range ((cochainTensorMap S.f (𝟙 S.X₂)).f n).hom ⊔
      LinearMap.range ((cochainTensorMap (𝟙 S.X₂) S.f).f n).hom := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have h₁ : (tensorSquareMap S.f).f n =
        (cochainTensorMap (𝟙 S.X₁) S.f).f n ≫ (cochainTensorMap S.f (𝟙 S.X₂)).f n := by
      rw [← HomologicalComplex.comp_f, cochainTensorMap_comp, id_comp, comp_id]
    have h₂ : cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n =
        cochainTensorDegreeMap (fun i => 𝟙 (S.X₁.X i)) (cochainSplittingSection S σ) n ≫
          (cochainTensorMap S.f (𝟙 S.X₂)).f n := by
      rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
      simp only [HomologicalComplex.id_f, id_comp, comp_id]
    have h₃ : cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n =
        cochainTensorDegreeMap (cochainSplittingSection S σ) (fun i => 𝟙 (S.X₁.X i)) n ≫
          (cochainTensorMap (𝟙 S.X₂) S.f).f n := by
      rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
      simp only [HomologicalComplex.id_f, id_comp, comp_id]
    have he := congrArg (fun f => f.hom x)
      (tensorSquareKernelInclusion_decomposition S hS hproj σ n)
    simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply] at he
    rw [he]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply (le_sup_left : LinearMap.range ((cochainTensorMap S.f (𝟙 S.X₂)).f n).hom ≤ _)
        rw [h₁]
        exact ⟨_, rfl⟩
      · apply (le_sup_left : LinearMap.range ((cochainTensorMap S.f (𝟙 S.X₂)).f n).hom ≤ _)
        rw [h₂]
        exact ⟨_, rfl⟩
    · apply (le_sup_right : LinearMap.range ((cochainTensorMap (𝟙 S.X₂) S.f).f n).hom ≤ _)
      rw [h₃]
      exact ⟨_, rfl⟩
  · apply sup_le
    · rintro y ⟨x, rfl⟩
      refine ⟨((tensorSquareKernelPartialLeft S).f n).hom x, ?_⟩
      exact congrArg (fun f => f.f n |>.hom x) (tensorSquareKernelPartialLeft_inclusion S)
    · rintro y ⟨x, rfl⟩
      refine ⟨((tensorSquareKernelPartialRight S).f n).hom x, ?_⟩
      exact congrArg (fun f => f.f n |>.hom x) (tensorSquareKernelPartialRight_inclusion S)

end Adams
end SerrePositivity
