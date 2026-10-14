module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedReconstruction

/-! # Exactness of the low tensor-cube mixed quotient -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
private lemma three_component_total {C : Type*} [Category C] [Preadditive C]
    {A K Y Y₀ Y₁ Y₂ : C} (r : K ⟶ A) (f : A ⟶ K) (g : K ⟶ Y)
    (p₀ : Y ⟶ Y₀) (p₁ : Y ⟶ Y₁) (p₂ : Y ⟶ Y₂)
    (d₀ : Y₀ ⟶ K) (d₁ : Y₁ ⟶ K) (d₂ : Y₂ ⟶ K)
    (m₀ : K ⟶ Y₀) (m₁ : K ⟶ Y₁) (m₂ : K ⟶ Y₂)
    (h₀ : g ≫ p₀ = m₀) (h₁ : g ≫ p₁ = m₁) (h₂ : g ≫ p₂ = m₂)
    (ht : r ≫ f + m₀ ≫ d₀ + m₁ ≫ d₁ + m₂ ≫ d₂ = 𝟙 K) :
    r ≫ f + g ≫ (p₀ ≫ d₀ + p₁ ≫ d₁ + p₂ ≫ d₂) = 𝟙 K := by
  rw [comp_add, comp_add, ← Category.assoc, ← Category.assoc, ← Category.assoc,
    h₀, h₁, h₂, ← add_assoc, ← add_assoc]
  exact ht

variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeLowMixedSplitting_identity
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (n : ℤ) :
    tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n +
      (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedSectionX S σ n =
        𝟙 ((tensorCubeFirstLayer S.g).X n) := by
  exact three_component_total
    (tensorCubeLowMixedRetractionX S σ n) ((tensorCubeFirstLayerFirstMap S).f n)
    ((tensorCubeLowMixedMap S hS hproj).f n)
    (tensorCubeLowMixedProjection0X S n) (tensorCubeLowMixedProjection1X S n)
    (tensorCubeLowMixedProjection2X S n)
    (tensorCubeLowMixedSection0X S σ n) (tensorCubeLowMixedSection1X S σ n)
    (tensorCubeLowMixedSection2X S σ n)
    ((tensorCubeLowMixed0 S hS hproj).f n) ((tensorCubeLowMixed1 S hS hproj).f n)
    ((tensorCubeLowMixed2 S hS hproj).f n)
    (tensorCubeLowMixedMap_projection0X S hS hproj n)
    (tensorCubeLowMixedMap_projection1X S hS hproj n)
    (tensorCubeLowMixedMap_projection2X S hS hproj n)
    (tensorCubeLowMixedSplitting_total S σ hS hproj n)

set_option maxHeartbeats 600000 in
-- Evaluation of the nested-kernel sequence needs normalization of its three structure fields.
/-- The low mixed short complex splits in every degree. -/
def tensorCubeLowMixedSplitting
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting) (n : ℤ) :
    ((tensorCubeLowMixedShortComplex S hS hproj).map (eval _ _ n)).Splitting where
  r := tensorCubeLowMixedRetractionX S σ n
  s := tensorCubeLowMixedSectionX S σ n
  f_r := tensorCubeLowMixedRetractionX_retract S σ n
  s_g := tensorCubeLowMixedSectionX_section S σ hS hproj n
  id := by
    change tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n +
      (tensorCubeLowMixedMap S hS hproj).f n ≫ tensorCubeLowMixedSectionX S σ n =
        𝟙 ((tensorCubeFirstLayer S.g).X n)
    exact tensorCubeLowMixedSplitting_identity S hS hproj σ n

lemma tensorCubeLowMixedShortComplex_shortExact :
    (tensorCubeLowMixedShortComplex S hS hproj).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n =>
    (tensorCubeLowMixedSplitting S hS hproj
      (cochainDegreewiseSplittingOfProjective S hS hproj) n).shortExact)

/-- Compare the chosen cokernel of a short exact sequence with its final object. -/
def shortExactCokernelIso
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel T.f ≅ T.X₃ :=
  (cokernelIsCokernel T.f).coconePointUniqueUpToIso hT.gIsCokernel

private lemma shortExactCokernelIso_π_hom
    {C : Type*} [Category C] [Abelian C] (T : ShortComplex C) (hT : T.ShortExact) :
    cokernel.π T.f ≫ (shortExactCokernelIso T hT).hom = T.g :=
  (cokernelIsCokernel T.f).comp_coconePointUniqueUpToIso_hom
    hT.gIsCokernel WalkingParallelPair.one

set_option maxHeartbeats 600000 in
-- Compare the cokernel model with the explicitly named first-layer map and target.
/-- The quotient of the first layer by AAA is the three low mixed components. -/
def tensorCubeLowMixedCokernelIso : cokernel (tensorCubeFirstLayerFirstMap S) ≅
    tensorCubeLowMixedTarget S :=
  shortExactCokernelIso _ (tensorCubeLowMixedShortComplex_shortExact S hS hproj)

set_option maxHeartbeats 600000 in
-- The comparison of cokernel projections reduces the same nested models.
lemma tensorCubeLowMixedCokernelIso_π_hom :
    cokernel.π (tensorCubeFirstLayerFirstMap S) ≫ (tensorCubeLowMixedCokernelIso S hS hproj).hom =
      tensorCubeLowMixedMap S hS hproj :=
  shortExactCokernelIso_π_hom _ (tensorCubeLowMixedShortComplex_shortExact S hS hproj)

end Adams
end SerrePositivity
