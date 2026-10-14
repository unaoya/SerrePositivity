module

public import SerrePositivity.KTheory.Adams.TensorSquareMixed

/-! # Degreewise splittings of the mixed tensor-square sequence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

namespace Adams
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
  (hproj : ∀ i, Module.Projective R (S.X₃.X i))
  (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

lemma tensorSquareMixedSplitting_f_g :
    (fun i => S.f.f i ≫ S.g.f i) = (fun i => (0 : S.X₁.X i ⟶ S.X₃.X i)) := by
  funext i
  exact congrArg (fun f => f.f i) S.zero

/-- The degreewise retraction onto the first tensor-square layer. -/
def tensorSquareMixedRetractionX (n : ℤ) : (tensorSquareKernel S.g).X n ⟶ (tensorSquare S.X₁).X n :=
  (tensorSquareKernelInclusion S.g).f n ≫
    cochainTensorDegreeMap (cochainSplittingRetraction S σ) (cochainSplittingRetraction S σ) n

lemma tensorSquareMixedRetractionX_retract (n : ℤ) :
    (tensorSquareKernelFirstMap S).f n ≫ tensorSquareMixedRetractionX S σ n = 𝟙 _ := by
  rw [tensorSquareMixedRetractionX, ← HomologicalComplex.comp_f_assoc,
    tensorSquareKernelFirstMap_inclusion]
  rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
  have h : (fun i => S.f.f i ≫ cochainSplittingRetraction S σ i) =
      (fun i => 𝟙 (S.X₁.X i)) := funext fun i => (σ i).f_r
  rw [h, cochainTensorDegreeMap_id]

/-- A degreewise lift of the left mixed component into the intermediate layer. -/
def tensorSquareMixedSectionLeftX (n : ℤ) :
    (cochainTensor S.X₁ S.X₃).X n ⟶ (tensorSquareKernel S.g).X n := by
  have hT := tensorSquareKernelShortComplex_shortExact S hS hproj
  have := hT.mono_f
  have := hT.epi_g
  have hN := hT.map (eval _ _ n)
  have := hN.mono_f
  exact hN.exact.lift (cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n) (by
    change cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n ≫
      (tensorSquareMap S.g).f n = 0
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp,
      tensorSquareMixedSplitting_f_g, cochainTensorDegreeMap_zero_left])

@[reassoc]
lemma tensorSquareMixedSectionLeftX_inclusion (n : ℤ) :
    tensorSquareMixedSectionLeftX S hS hproj σ n ≫ (tensorSquareKernelInclusion S.g).f n =
      cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n := by
  dsimp [tensorSquareMixedSectionLeftX]
  exact Fork.IsLimit.lift_ι _

/-- A degreewise lift of the right mixed component into the intermediate layer. -/
def tensorSquareMixedSectionRightX (n : ℤ) :
    (cochainTensor S.X₃ S.X₁).X n ⟶ (tensorSquareKernel S.g).X n := by
  have hT := tensorSquareKernelShortComplex_shortExact S hS hproj
  have := hT.mono_f
  have := hT.epi_g
  have hN := hT.map (eval _ _ n)
  have := hN.mono_f
  exact hN.exact.lift (cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n) (by
    change cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n ≫
      (tensorSquareMap S.g).f n = 0
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp,
      tensorSquareMixedSplitting_f_g, cochainTensorDegreeMap_zero_right])

@[reassoc]
lemma tensorSquareMixedSectionRightX_inclusion (n : ℤ) :
    tensorSquareMixedSectionRightX S hS hproj σ n ≫ (tensorSquareKernelInclusion S.g).f n =
      cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n := by
  dsimp [tensorSquareMixedSectionRightX]
  exact Fork.IsLimit.lift_ι _

@[reassoc]
lemma tensorSquareMixedLeft_inclusion_f (n : ℤ) :
    (tensorSquareMixedLeft S hS hproj).f n ≫ (cochainTensorMap S.f (𝟙 S.X₃)).f n =
      (tensorSquareKernelInclusion S.g).f n ≫ (cochainTensorMap (𝟙 S.X₂) S.g).f n :=
  congrArg (fun f => f.f n) (tensorSquareMixedLeft_inclusion S hS hproj)

@[reassoc]
lemma tensorSquareMixedRight_inclusion_f (n : ℤ) :
    (tensorSquareMixedRight S hS hproj).f n ≫ (cochainTensorMap (𝟙 S.X₃) S.f).f n =
      (tensorSquareKernelInclusion S.g).f n ≫ (cochainTensorMap S.g (𝟙 S.X₂)).f n :=
  congrArg (fun f => f.f n) (tensorSquareMixedRight_inclusion S hS hproj)

lemma tensorSquareMixedSectionLeftX_left (n : ℤ) :
    tensorSquareMixedSectionLeftX S hS hproj σ n ≫ (tensorSquareMixedLeft S hS hproj).f n =
      𝟙 _ := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap S.f (𝟙 S.X₃)).f n)).1
  rw [Category.assoc, tensorSquareMixedLeft_inclusion_f,
    tensorSquareMixedSectionLeftX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, id_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have h : (fun j => cochainSplittingSection S σ j ≫ S.g.f j) =
      (fun j => 𝟙 (S.X₃.X j)) := funext fun j => (σ j).s_g
  rw [h]
  exact cochainTensorDegreeMap_eq S.f (𝟙 S.X₃) n

lemma tensorSquareMixedSectionLeftX_right (n : ℤ) :
    tensorSquareMixedSectionLeftX S hS hproj σ n ≫ (tensorSquareMixedRight S hS hproj).f n =
      0 := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Mono (cochainTensorMap (𝟙 S.X₃) S.f) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap (𝟙 S.X₃) S.f).f n)).1
  rw [Category.assoc, tensorSquareMixedRight_inclusion_f,
    tensorSquareMixedSectionLeftX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, tensorSquareMixedSplitting_f_g,
    cochainTensorDegreeMap_zero_left, zero_comp]

lemma tensorSquareMixedSectionRightX_left (n : ℤ) :
    tensorSquareMixedSectionRightX S hS hproj σ n ≫ (tensorSquareMixedLeft S hS hproj).f n =
      0 := by
  have hT := cochainTensorShortComplexRight_shortExact_of_projective S hS hproj S.X₃
  have : Mono (cochainTensorMap S.f (𝟙 S.X₃)) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap S.f (𝟙 S.X₃)).f n)).1
  rw [Category.assoc, tensorSquareMixedLeft_inclusion_f,
    tensorSquareMixedSectionRightX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, tensorSquareMixedSplitting_f_g,
    cochainTensorDegreeMap_zero_right, zero_comp]

lemma tensorSquareMixedSectionRightX_right (n : ℤ) :
    tensorSquareMixedSectionRightX S hS hproj σ n ≫ (tensorSquareMixedRight S hS hproj).f n =
      𝟙 _ := by
  have hT := cochainTensorShortComplexLeft_shortExact_of_projective S.X₃ S hS hproj
  have : Mono (cochainTensorMap (𝟙 S.X₃) S.f) := hT.mono_f
  apply (cancel_mono ((cochainTensorMap (𝟙 S.X₃) S.f).f n)).1
  rw [Category.assoc, tensorSquareMixedRight_inclusion_f,
    tensorSquareMixedSectionRightX_inclusion_assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp, id_comp]
  simp only [HomologicalComplex.id_f, comp_id]
  have h : (fun i => cochainSplittingSection S σ i ≫ S.g.f i) =
      (fun i => 𝟙 (S.X₃.X i)) := funext fun i => (σ i).s_g
  rw [h]
  exact cochainTensorDegreeMap_eq (𝟙 S.X₃) S.f n

lemma tensorSquareMixedRetractionX_first_inclusion (n : ℤ) :
    tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n ≫
      (tensorSquareKernelInclusion S.g).f n = (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i)
        (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i) n := by
  rw [← HomologicalComplex.comp_f, tensorSquareKernelFirstMap_inclusion,
    tensorSquareMixedRetractionX, Category.assoc, ← cochainTensorDegreeMap_eq,
    cochainTensorDegreeMap_comp]

lemma tensorSquareMixedLeft_section_inclusion (n : ℤ) :
    (tensorSquareMixedLeft S hS hproj).f n ≫ tensorSquareMixedSectionLeftX S hS hproj σ n ≫
      (tensorSquareKernelInclusion S.g).f n = (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => 𝟙 (S.X₂.X i))
        (fun i => S.g.f i ≫ cochainSplittingSection S σ i) n := by
  rw [tensorSquareMixedSectionLeftX_inclusion]
  have he : cochainTensorDegreeMap S.f.f (cochainSplittingSection S σ) n =
      (cochainTensorMap S.f (𝟙 S.X₃)).f n ≫
        cochainTensorDegreeMap (fun i => 𝟙 (S.X₂.X i)) (cochainSplittingSection S σ) n := by
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, tensorSquareMixedLeft_inclusion_f, Category.assoc,
    ← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]

lemma tensorSquareMixedRight_section_inclusion (n : ℤ) :
    (tensorSquareMixedRight S hS hproj).f n ≫
      tensorSquareMixedSectionRightX S hS hproj σ n ≫
      (tensorSquareKernelInclusion S.g).f n = (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => S.g.f i ≫ cochainSplittingSection S σ i)
        (fun i => 𝟙 (S.X₂.X i)) n := by
  rw [tensorSquareMixedSectionRightX_inclusion]
  have he : cochainTensorDegreeMap (cochainSplittingSection S σ) S.f.f n =
      (cochainTensorMap (𝟙 S.X₃) S.f).f n ≫
        cochainTensorDegreeMap (cochainSplittingSection S σ) (fun i => 𝟙 (S.X₂.X i)) n := by
    rw [← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
    simp only [HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, tensorSquareMixedRight_inclusion_f, Category.assoc,
    ← cochainTensorDegreeMap_eq, cochainTensorDegreeMap_comp]
  simp only [HomologicalComplex.id_f, comp_id]

lemma tensorSquareMixed_doubleQuotient_zero (n : ℤ) :
    (tensorSquareKernelInclusion S.g).f n ≫
      cochainTensorDegreeMap (fun i => S.g.f i ≫ cochainSplittingSection S σ i)
        (fun i => S.g.f i ≫ cochainSplittingSection S σ i) n = 0 := by
  rw [← cochainTensorDegreeMap_comp, cochainTensorDegreeMap_eq S.g S.g n,
    ← Category.assoc, ← HomologicalComplex.comp_f, kernel.condition]
  simp

/-- The first and two mixed components reconstruct every element of the intermediate layer. -/
lemma tensorSquareMixedSplitting_total (n : ℤ) :
    tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n +
      (tensorSquareMixedLeft S hS hproj).f n ≫
    tensorSquareMixedSectionLeftX S hS hproj σ n +
      (tensorSquareMixedRight S hS hproj).f n ≫
      tensorSquareMixedSectionRightX S hS hproj σ n =
      𝟙 ((tensorSquareKernel S.g).X n) := by
  apply (cancel_mono ((tensorSquareKernelInclusion S.g).f n)).1
  rw [add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc,
    tensorSquareMixedRetractionX_first_inclusion, tensorSquareMixedLeft_section_inclusion,
    tensorSquareMixedRight_section_inclusion, id_comp, ← comp_add, ← comp_add]
  have h : (fun i => cochainSplittingRetraction S σ i ≫ S.f.f i +
      S.g.f i ≫ cochainSplittingSection S σ i) = (fun i => 𝟙 (S.X₂.X i)) :=
    funext fun i => (σ i).id
  rw [cochainTensorDegreeMap_partition _ _ h, comp_add, comp_id,
    tensorSquareMixed_doubleQuotient_zero, add_zero]

abbrev cochainBiprodFstX (A B : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (A ⊞ B).X n ⟶ A.X n := (biprod.fst : A ⊞ B ⟶ A).f n

abbrev cochainBiprodSndX (A B : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (A ⊞ B).X n ⟶ B.X n := (biprod.snd : A ⊞ B ⟶ B).f n

lemma cochainBiprodX_hom_ext
    (A B : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) {W : ModuleCat.{u} R}
    (f g : W ⟶ (A ⊞ B).X n)
    (hf : f ≫ (biprod.fst : A ⊞ B ⟶ A).f n = g ≫ cochainBiprodFstX A B n)
    (hg : f ≫ (biprod.snd : A ⊞ B ⟶ B).f n = g ≫ cochainBiprodSndX A B n) : f = g := by
  apply (isLimitOfPreserves (eval (ModuleCat.{u} R) (.up ℤ) n)
    (BinaryBiproduct.isLimit A B)).hom_ext
  rintro ⟨j⟩
  cases j
  · exact hf
  · exact hg

@[reassoc]
lemma tensorSquareMixedMap_fst_f (n : ℤ) :
    (tensorSquareMixedMap S hS hproj).f n ≫
      cochainBiprodFstX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n =
      (tensorSquareMixedLeft S hS hproj).f n :=
  congrArg (fun f => f.f n) (biprod.lift_fst
    (tensorSquareMixedLeft S hS hproj) (tensorSquareMixedRight S hS hproj))

@[reassoc]
lemma tensorSquareMixedMap_snd_f (n : ℤ) :
    (tensorSquareMixedMap S hS hproj).f n ≫
      cochainBiprodSndX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n =
      (tensorSquareMixedRight S hS hproj).f n :=
  congrArg (fun f => f.f n) (biprod.lift_snd
    (tensorSquareMixedLeft S hS hproj) (tensorSquareMixedRight S hS hproj))

/-- The two component lifts combine into a degreewise section of the mixed map. -/
def tensorSquareMixedSectionX (n : ℤ) :
    (cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁).X n ⟶ (tensorSquareKernel S.g).X n :=
  cochainBiprodFstX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n ≫
    tensorSquareMixedSectionLeftX S hS hproj σ n +
    cochainBiprodSndX (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n ≫
      tensorSquareMixedSectionRightX S hS hproj σ n

lemma tensorSquareMixedSectionX_section (n : ℤ) :
    tensorSquareMixedSectionX S hS hproj σ n ≫ (tensorSquareMixedMap S hS hproj).f n = 𝟙 _ := by
  apply cochainBiprodX_hom_ext (cochainTensor S.X₁ S.X₃) (cochainTensor S.X₃ S.X₁) n
  · rw [Category.assoc, tensorSquareMixedMap_fst_f, tensorSquareMixedSectionX,
      add_comp, Category.assoc, Category.assoc, tensorSquareMixedSectionLeftX_left,
      tensorSquareMixedSectionRightX_left, comp_id, comp_zero, add_zero, id_comp]
  · rw [Category.assoc, tensorSquareMixedMap_snd_f, tensorSquareMixedSectionX,
      add_comp, Category.assoc, Category.assoc, tensorSquareMixedSectionLeftX_right,
      tensorSquareMixedSectionRightX_right, comp_zero, comp_id, zero_add, id_comp]

/-- The inner mixed sequence splits in each degree. -/
def tensorSquareMixedSplitting (n : ℤ) :
    ((tensorSquareMixedShortComplex S hS hproj).map (eval _ _ n)).Splitting where
  r := tensorSquareMixedRetractionX S σ n
  s := tensorSquareMixedSectionX S hS hproj σ n
  f_r := tensorSquareMixedRetractionX_retract S σ n
  s_g := tensorSquareMixedSectionX_section S hS hproj σ n
  id := by
    change tensorSquareMixedRetractionX S σ n ≫ (tensorSquareKernelFirstMap S).f n +
      (tensorSquareMixedMap S hS hproj).f n ≫ tensorSquareMixedSectionX S hS hproj σ n =
      𝟙 ((tensorSquareKernel S.g).X n)
    rw [tensorSquareMixedSectionX, comp_add, ← Category.assoc, ← Category.assoc,
      tensorSquareMixedMap_fst_f, tensorSquareMixedMap_snd_f, ← add_assoc]
    exact tensorSquareMixedSplitting_total S hS hproj σ n

/-- The canonical inner sequence of the tensor-square filtration is short exact. -/
lemma tensorSquareMixedShortComplex_shortExact :
    (tensorSquareMixedShortComplex S hS hproj).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (tensorSquareMixedSplitting S hS hproj
      (cochainDegreewiseSplittingOfProjective S hS hproj) n).shortExact)

/-- The quotient of the intermediate layer by the first layer is the mixed complex. -/
def tensorSquareMixedCokernelIso : cokernel (tensorSquareKernelFirstMap S) ≅
    cochainTensor S.X₁ S.X₃ ⊞ cochainTensor S.X₃ S.X₁ :=
  (cokernelIsCokernel (tensorSquareKernelFirstMap S)).coconePointUniqueUpToIso
    (tensorSquareMixedShortComplex_shortExact S hS hproj).gIsCokernel

@[reassoc]
lemma tensorSquareMixedCokernelIso_π_hom :
    cokernel.π (tensorSquareKernelFirstMap S) ≫ (tensorSquareMixedCokernelIso S hS hproj).hom =
      tensorSquareMixedMap S hS hproj :=
  (cokernelIsCokernel (tensorSquareKernelFirstMap S)).comp_coconePointUniqueUpToIso_hom
    (tensorSquareMixedShortComplex_shortExact S hS hproj).gIsCokernel WalkingParallelPair.one

end Adams
end SerrePositivity
