module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ArrowTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorLiftingClass
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-! # Relative subcomplex tensors of Reedy cofibrations

Finite skeletal attachments in the arrow category prove the cofibration
condition. For horns, homotopical constancy of both frames supplies the
weak equivalence by pushout of a trivial cofibration and two-out-of-three.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {A B : SimplexCategory ⥤ C} (α : A ⟶ B)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (hα : reedyLeft simplex (cofibrations C) α)

abbrev relativeSubcomplexTensorMap {n : SimplexCategory}
    (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) :=
  HomPresentation.relativeTensorMap (SubcomplexTensor.diagram S) α
    (SubcomplexTensor.simplexCocone S)

include hA hα in
lemma relativeSubcomplexTensor_cofibration {n : SimplexCategory}
    (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) :
    cofibrations C (relativeSubcomplexTensorMap α S) := by
  let Q := trivialFibrations C
  let P := ArrowLiftingClass.objectwise Q
  have hb (d : ℕ) : P.llp
      (FiniteTensor.map (ArrowTensor.diagram α) (SSet.boundary.{v} d).ι) := by
    apply (P.llp.arrow_iso_iff (finiteTensorInclusionArrowIso (ArrowTensor.diagram α) _)).mpr
    apply (P.llp.arrow_iso_iff (ArrowTensor.inclusionArrowIso α _)).mpr
    apply ArrowLiftingClass.mem_of_left_and_relative Q
    · change (trivialFibrations C).llp (SubcomplexTensor.inclusion (SSet.boundary.{v} d) A)
      rw [trivialFibrations_llp C]
      exact boundaryTensor_cofibration A d hA
    · change (trivialFibrations C).llp (relativeBoundaryTensorMap α d)
      rw [trivialFibrations_llp C]
      exact ((cofibrations C).arrow_iso_iff (relativeBoundaryTensorArrowIso α d)).mpr
        (hα (SimplexCategory.mk d))
  have h := FiniteTensor.LiftingClass.map_mono_mem (ArrowTensor.diagram α) P hb S.ι
  have h' := (P.llp.arrow_iso_iff
    (finiteTensorInclusionArrowIso (ArrowTensor.diagram α) S)).mp h
  have h'' := (P.llp.arrow_iso_iff (ArrowTensor.inclusionArrowIso α S)).mp h'
  have hr := ArrowLiftingClass.relative_mem_of_mem Q (ArrowTensor.inclusionSquare α S) h''
  change (trivialFibrations C).llp (relativeSubcomplexTensorMap α S) at hr
  rwa [trivialFibrations_llp C] at hr

include hA hα in
lemma relativeHornTensor_trivialCofibration
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (hconstA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hconstB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (d : ℕ) (i : Fin (d + 2)) :
    trivialCofibrations C (relativeSubcomplexTensorMap α (SSet.horn.{v} (d + 1) i)) := by
  refine ⟨relativeSubcomplexTensor_cofibration α hA hα _, ?_⟩
  let S := SSet.horn.{v} (d + 1) i
  have hA' := hornTensor_trivialCofibration A hA hconstA d i
  have hB' := hornTensor_trivialCofibration B hB hconstB d i
  have hp : trivialCofibrations C
      (pushout.inl (HomPresentation.tensorSourceMap (SubcomplexTensor.diagram S) α)
        (SubcomplexTensor.inclusion S A)) :=
    (trivialCofibrations C).of_isPushout
      (IsPushout.of_hasPushout _ _) hA'
  have he := HomPresentation.inl_relativeTensorMap (SubcomplexTensor.diagram S) α
    (SubcomplexTensor.simplexCocone S)
  exact (weakEquivalences C).of_precomp _ _ hp.2 (he.symm ▸ hB'.2)

include hA hα in
/-- Source restriction between cosimplicial frames is a Kan fibration at a fibrant target. -/
lemma cosimplicialHomMap_hornRLP
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (hconstA : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    (hconstB : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (B.map f))
    (targetObject : C) [IsFibrant targetObject] :
    SSet.modelCategoryQuillen.J.{v}.rlp ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app targetObject) := by
  intro K L f hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  have ht := relativeHornTensor_trivialCofibration α hA hα hB hconstA hconstB n i
  have : HasLiftingProperty
      (relativeSubcomplexTensorMap α (SSet.horn.{v} (n + 1) i))
      (terminal.from targetObject) :=
    MorphismProperty.hasLiftingProperty_of_wfs _ _ ht (mem_fibrations (terminal.from targetObject))
  have hl := HomPresentation.source_hasLiftingProperty
    (SubcomplexTensor.diagram (SSet.horn.{v} (n + 1) i))
    (NonsingularPresentation.cocone (SSet.horn.{v} (n + 1) i).toSSet)
    (NonsingularPresentation.isColimit (SSet.horn.{v} (n + 1) i).toSSet) α
    (SubcomplexTensor.simplexCocone (SSet.horn.{v} (n + 1) i)) (Y := targetObject)
  rwa [SubcomplexTensor.presentationMap_eq] at hl

end SerrePositivity.HomotopyFunctionComplex
