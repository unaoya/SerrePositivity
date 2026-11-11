module

public import SerrePositivity.HomotopicalAlgebra.Localization.LocalBoundaryGenerators
public import SerrePositivity.HomotopicalAlgebra.Localization.LocalFibrantApproximation
public import SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrameFibrations
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationSourceLiftingConverse

/-! # Exact boundary lifting characterization of fibrant local objects

The small family already used for LocalFibrantApproximation is now also
necessary for locality. This does not assert that its generated cells are
local equivalences or that the approximation unit is a local equivalence.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield.LocalBoundaryGenerators
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma rlp_of_localObjects (S : MorphismProperty C) (targetObject : C) [IsFibrant targetObject]
    (hY : localObjects cof fib S targetObject) :
    (generators cof S).rlp (terminal.from targetObject) := by
  rintro X Z g ⟨⟨⟨f, hf⟩, n⟩⟩
  have ht := ArrowFrames.testMap_trivialFibration_of_local cof fib hcof hfib S targetObject hY f hf
  have hr : (MorphismProperty.monomorphisms SSet.{v}).rlp
      (ArrowFrames.testMap cof f targetObject) := by
    rw [← hcof, MorphismProperty.rlp_eq_of_wfs (cofibrations SSet.{v})
      (trivialFibrations SSet.{v})]
    exact ht
  have : HasLiftingProperty (SSet.boundary.{v} n).ι (ArrowFrames.testMap cof f targetObject) :=
    hr _ (by change Mono _; infer_instance)
  have hp : HasLiftingProperty
      (HomPresentation.presentationMap (SubcomplexTensor.diagram (SSet.boundary.{v} n))
        (NonsingularPresentation.cocone (SSet.boundary.{v} n).toSSet)
        (NonsingularPresentation.isColimit (SSet.boundary.{v} n).toSSet)
        (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n)))
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((ArrowFrames.inclusion cof).app f)).app targetObject) := by
    rw [SubcomplexTensor.presentationMap_eq]
    exact inferInstanceAs (HasLiftingProperty (SSet.boundary.{v} n).ι
      (ArrowFrames.testMap cof f targetObject))
  have hl := HomPresentation.relativeTensor_hasLiftingProperty
    (SubcomplexTensor.diagram (SSet.boundary.{v} n))
    (NonsingularPresentation.cocone (SSet.boundary.{v} n).toSSet)
    (NonsingularPresentation.isColimit (SSet.boundary.{v} n).toSSet)
    ((ArrowFrames.inclusion cof).app f)
    (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n)) targetObject
  exact (HasLiftingProperty.iff_of_arrow_iso_left
    (relativeBoundaryTensorArrowIso ((ArrowFrames.inclusion cof).app f) n)
    (terminal.from targetObject)).mp hl

include hcof hfib in
lemma localObjects_iff_rlp (S : MorphismProperty C) (Y : C) [IsFibrant Y] :
    localObjects cof fib S Y ↔ (generators cof S).rlp (terminal.from Y) :=
  ⟨rlp_of_localObjects cof fib hcof hfib S Y, localObjects_of_rlp cof S hcof fib Y⟩

include hcof hfib in
lemma localFibrantObjects_iff_rlp (I J : MorphismProperty C)
    [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] (S : MorphismProperty C) (Y : C) :
    localFibrantObjects cof fib S Y ↔
      (LocalFibrantApproximation.generators J cof S).rlp (terminal.from Y) := by
  constructor
  · rintro ⟨hF, hL⟩
    have := hF
    have hJ : J.rlp (terminal.from Y) := by
      rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_J (I := I) (J := J)]
      exact mem_fibrations (terminal.from Y)
    have hS := rlp_of_localObjects cof fib hcof hfib S Y hL
    intro X Z g hg
    rcases hg with hg | hg
    · exact hJ g hg
    · exact hS g hg
  · exact LocalFibrantApproximation.localFibrant_of_rlp I J cof S fib hcof Y

end SerrePositivity.Bousfield.LocalBoundaryGenerators
