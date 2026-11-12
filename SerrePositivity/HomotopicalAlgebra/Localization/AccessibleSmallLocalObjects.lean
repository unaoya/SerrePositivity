module

public import SerrePositivity.HomotopicalAlgebra.Localization.SmallHomTests
public import SerrePositivity.HomotopicalAlgebra.Localization.MappingTestDiagram
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomAccessible
public import SerrePositivity.HomotopicalAlgebra.Smith.AccessibleWeakEquivalenceInverseImage
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility

/-! # Accessibility of the actual small-Hom local-object category

The whole fixed family is tested by one arrow in an actual projective
diagram model. The proved weak-equivalence inverse-image theorem supplies
accessibility of the local category and of its actual inclusion together.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}]

lemma exists_accessible_smallLocalObjects
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    {ι : Type w} (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory
          (smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData
            (MorphismProperty.ofHoms (fun i => (s i).hom)))) κ ∧
        (ObjectProperty.ι (smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData
          (MorphismProperty.ofHoms (fun i => (s i).hom)))).IsCardinalAccessible κ := by
  have := SmallHomComparison.exists_accessible_mapping_tests I J s
  obtain ⟨κ₀, h₀, d₀, _, _, hs, _⟩ := this
  let M := SmallHomComparison.chosenHom d₀.cofibrationData d₀.fibrationData
  let F := MappingTestDiagram.arrow M s
  have : ∀ i, (M.obj (Opposite.op (s i).left)).IsCardinalAccessible κ₀ := fun i => (hs i).1
  have : ∀ i, (M.obj (Opposite.op (s i).right)).IsCardinalAccessible κ₀ := fun i => (hs i).2
  have : F.IsCardinalAccessible κ₀ := MappingTestDiagram.arrow_isCardinalAccessible M s κ₀
  have : F.IsAccessible.{w} := F.isAccessible_of_isCardinalAccessible κ₀
  have := DiagramModel.WeightedCones.simplicialSet_isLocallyPresentable.{w}
  have := SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  let := DiagramModel.Projective.modelCategory (Discrete ι)
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J
  have := DiagramModel.Projective.modelCategory_generated (Discrete ι)
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J
  have := Smith.AccessibleLimits.functorCategory_isLocallyPresentable
    (C := SSet.{w}) (Discrete ι)
  let P := (Smith.arrowProperty (weakEquivalences (Discrete ι ⥤ SSet.{w}))).inverseImage F
  have he : P = smallLocalObjects.{w, v, u} d₀.cofibrationData d₀.fibrationData
      (MorphismProperty.ofHoms (fun i => (s i).hom)) := by
    funext Y
    apply propext
    change (∀ i : Discrete ι, weakEquivalences SSet.{w}
        ((((MappingTestDiagram.arrow M s).obj Y).hom).app i)) ↔
      MorphismProperty.ofHoms (fun i => (s i).hom) ≤ smallMappingTest.{w, v, u}
        d₀.cofibrationData d₀.fibrationData Y
    rw [MorphismProperty.ofHoms_le_iff]
    exact ⟨fun h i => h ⟨i⟩, fun h ⟨i⟩ => h i⟩
  obtain ⟨ν, hν, hP, hinc⟩ := Smith.exists_accessible_weakEquivalence_inverseImage
    (DiagramModel.Projective.generators (Discrete ι) SSet.modelCategoryQuillen.I)
    (DiagramModel.Projective.generators (Discrete ι) SSet.modelCategoryQuillen.J) F
  obtain ⟨κ, hκ, h₀κ, hνκ⟩ := Cardinal.SharplyLT.exists_of_pair κ₀ ν
  let d := d₀.atLarger κ h₀κ.le
  have hP' : IsCardinalAccessibleCategory P.FullSubcategory κ :=
    hνκ.isCardinalAccessibleCategory _
  have hi' : P.ι.IsCardinalAccessible κ := Functor.isCardinalAccessible_of_le _ hνκ.le
  rw [he] at hP' hi'
  exact ⟨κ, hκ, d, hP', hi'⟩

lemma exists_accessible_smallLocalObjects_of_small
    (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
    (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory (ObjectProperty.FullSubcategory
          (smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData S)) κ ∧
        Functor.IsCardinalAccessible
          (ObjectProperty.ι
            (smallLocalObjects.{w, v, u} d.cofibrationData d.fibrationData S)) κ := by
  let s : Shrink.{w} S.toSet → Arrow C := fun i => ((equivShrink S.toSet).symm i).val
  have he : MorphismProperty.ofHoms (fun i => (s i).hom) = S := by
    ext X Y f
    rw [MorphismProperty.ofHoms_iff]
    constructor
    · rintro ⟨i, hi⟩
      change Arrow.mk f ∈ S.toSet
      rw [hi]
      exact ((equivShrink S.toSet).symm i).property
    · intro hf
      refine ⟨equivShrink S.toSet ⟨Arrow.mk f, hf⟩, ?_⟩
      simp [s]
  have h := exists_accessible_smallLocalObjects I J hcof hfib s
  rw [he] at h
  exact h

end SerrePositivity.Bousfield
