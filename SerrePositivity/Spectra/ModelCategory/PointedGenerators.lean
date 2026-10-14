module

public import SerrePositivity.Spectra.ModelCategory.SimplicialCofibrancy
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Actual pointed boundary and horn generators

Free basepoint addition transfers lifting tests. Its forgetful right adjoint
preserves filtered colimits, which suffices for presentability and the
small-object argument; preservation of all coproducts is not assumed.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
namespace SerrePositivity.SimplicialModelInputs
open SSet.modelCategoryQuillen
open SerrePositivity.ModelGeneration
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

abbrev pointedI : MorphismProperty PointedSimplicialSet.{u} :=
  I.strictMap PointedObject.adjoinFunctor
abbrev pointedJ : MorphismProperty PointedSimplicialSet.{u} :=
  J.strictMap PointedObject.adjoinFunctor

lemma pointedGenerators_rlp (P : MorphismProperty SSet.{u}) :
    (P.strictMap PointedObject.adjoinFunctor).rlp =
      P.rlp.inverseImage PointedSimplicialSet.forget := by
  ext A B f
  constructor
  · intro h X Y g hg
    exact (PointedObject.adjoinForgetAdjunction.hasLiftingProperty_iff g f).1
      (h _ (P.map_mem_strictMap _ g hg))
  · intro h X Y g hg
    cases hg with
    | map hg => exact (PointedObject.adjoinForgetAdjunction.hasLiftingProperty_iff _ f).2 (h _ hg)

/-- Filtered preservation of the actual Under forgetful functor. -/
lemma pointedForget_accessible :
    PointedSimplicialSet.forget.{u}.IsCardinalAccessible Cardinal.aleph0.{u} := by
  constructor
  intro J _ _
  let : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{u}
  let : IsConnected J := IsFiltered.isConnected J
  exact inferInstanceAs (PreservesColimitsOfShape J (Under.forget (𝟙_ SSet.{u})))

lemma pointedGenerator_domain_presentable (P : MorphismProperty SSet.{u})
    (hP : ∀ {A B : SSet.{u}} (f : A ⟶ B), P f → IsCardinalPresentable A Cardinal.aleph0.{u})
    {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : P.strictMap PointedObject.adjoinFunctor f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := by
  cases hf with
  | @map A B f hf =>
    have : IsCardinalPresentable A Cardinal.aleph0.{u} := hP f hf
    have := pointedForget_accessible
    exact PointedObject.adjoinForgetAdjunction.isCardinalPresentable_leftAdjoint_obj
      Cardinal.aleph0.{u} A

lemma pointedGenerators_smallObjectArgument (P : MorphismProperty SSet.{u}) [P.IsSmall.{u}]
    (hP : ∀ {A B : SSet.{u}} (f : A ⟶ B), P f → IsCardinalPresentable A Cardinal.aleph0.{u}) :
    (P.strictMap PointedObject.adjoinFunctor).HasSmallObjectArgument.{u} := by
  let L : PUnit.{1} → SSet.{u} ⥤ PointedSimplicialSet.{u} :=
    fun _ ↦ PointedObject.adjoinFunctor
  let R : PUnit.{1} → PointedSimplicialSet.{u} ⥤ SSet.{u} :=
    fun _ ↦ PointedSimplicialSet.forget
  let hR : ∀ i, (R i).IsCardinalAccessible Cardinal.aleph0.{u} :=
    fun _ ↦ pointedForget_accessible
  have h := @EvaluationFamily.generators_smallObjectArgument_of_accessible.{u}
    SSet.{u} _ PointedSimplicialSet.{u} _ PUnit.{1} _ L R
    (fun _ ↦ PointedObject.adjoinForgetAdjunction) _ _ P _ Cardinal.aleph0.{u} _ _ hR hP
  simpa only [EvaluationFamily.generators, L, iSup_unique] using h

lemma pointedI_smallObjectArgument : pointedI.{u}.HasSmallObjectArgument.{u} := by
  have : I.{u}.IsSmall.{u} := boundaryGenerators_isSmall
  exact pointedGenerators_smallObjectArgument I boundaryGenerator_domain_presentable

lemma pointedJ_smallObjectArgument : pointedJ.{u}.HasSmallObjectArgument.{u} :=
  pointedGenerators_smallObjectArgument J hornGenerator_domain_presentable

lemma pointedI_domain_presentable {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : pointedI f) : IsCardinalPresentable A Cardinal.aleph0.{u} :=
  pointedGenerator_domain_presentable I boundaryGenerator_domain_presentable f hf

lemma pointedJ_domain_presentable {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : pointedJ f) : IsCardinalPresentable A Cardinal.aleph0.{u} :=
  pointedGenerator_domain_presentable J hornGenerator_domain_presentable f hf

/-- The actual pointed horn generators detect the inherited Kan fibrations. -/
lemma pointedJ_rlp : pointedJ.{u}.rlp = fibrations PointedSimplicialSet.{u} := by
  rw [pointedGenerators_rlp, fibrations_under_def, MorphismProperty.under_eq_inverseImage]
  rfl

end SerrePositivity.SimplicialModelInputs
