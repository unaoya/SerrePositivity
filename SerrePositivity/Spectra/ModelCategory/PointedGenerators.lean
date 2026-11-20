module
public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationSmallness

public import SerrePositivity.Spectra.ModelCategory.SimplicialCofibrancy
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import SerrePositivity.CategoryTheory.Under


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
  have : I.{u}.IsSmall.{u} := _root_.SerrePositivity.SimplicialModel.boundaryGenerators_isSmall
  exact pointedGenerators_smallObjectArgument I _root_.SerrePositivity.SimplicialModel.boundaryGenerator_domain_presentable

lemma pointedJ_smallObjectArgument : pointedJ.{u}.HasSmallObjectArgument.{u} :=
  pointedGenerators_smallObjectArgument J _root_.SerrePositivity.SimplicialModel.hornGenerator_domain_presentable

lemma pointedI_domain_presentable {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : pointedI f) : IsCardinalPresentable A Cardinal.aleph0.{u} :=
  pointedGenerator_domain_presentable I _root_.SerrePositivity.SimplicialModel.boundaryGenerator_domain_presentable f hf

lemma pointedJ_domain_presentable {A B : PointedSimplicialSet.{u}} (f : A ⟶ B)
    (hf : pointedJ f) : IsCardinalPresentable A Cardinal.aleph0.{u} :=
  pointedGenerator_domain_presentable J _root_.SerrePositivity.SimplicialModel.hornGenerator_domain_presentable f hf

/-- The actual pointed horn generators detect the inherited Kan fibrations. -/
lemma pointedJ_rlp : pointedJ.{u}.rlp = fibrations PointedSimplicialSet.{u} := by
  rw [pointedGenerators_rlp, fibrations_under_def, MorphismProperty.under_eq_inverseImage]
  rfl

/-- Free pointed boundaries generate exactly the inherited mono cofibrations. -/
lemma pointedI_leftClass : pointedI.{u}.rlp.llp = cofibrations PointedSimplicialSet.{u} := by
  rw [pointedGenerators_rlp, cofibrations_under_def]
  change (I.{u}.rlp.under (X := 𝟙_ SSet.{u})).llp =
    (MorphismProperty.monomorphisms SSet.{u}).under
  let : I.{u}.HasSmallObjectArgument.{u} := _root_.SerrePositivity.SimplicialModel.boundaryGenerators_smallObjectArgument
  have hfac : (MorphismProperty.monomorphisms SSet.{u}).HasFactorization I.rlp := by
    rw [← _root_.SerrePositivity.SimplicialModel.boundaryGenerators_leftClass]
    infer_instance
  let : (MorphismProperty.monomorphisms SSet.{u}).HasFactorization I.rlp := hfac
  have hret : ((MorphismProperty.monomorphisms SSet.{u}).under
      (X := 𝟙_ SSet.{u})).IsStableUnderRetracts := by
    rw [MorphismProperty.under_eq_inverseImage]
    infer_instance
  let : ((MorphismProperty.monomorphisms SSet.{u}).under
      (X := 𝟙_ SSet.{u})).IsStableUnderRetracts := hret
  apply MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
  intro A B i hi X Y p hp
  have hi' : I.rlp.llp i.right := by
    rw [_root_.SerrePositivity.SimplicialModel.boundaryGenerators_leftClass]
    exact hi
  let : HasLiftingProperty i.right p.right := hi' _ hp
  exact HasLiftingProperty.under i p

/-- The concrete pointed cofibration/lifting pair is a weak factorization system. -/
lemma pointedI_weakFactorizationSystem :
    MorphismProperty.IsWeakFactorizationSystem
      (cofibrations PointedSimplicialSet.{u}) pointedI.rlp := by
  let : pointedI.{u}.HasSmallObjectArgument.{u} := pointedI_smallObjectArgument
  rw [← pointedI_leftClass]
  infer_instance

/-- The concrete pointed boundary factorization can be chosen functorially. -/
lemma pointedI_functorialFactorization :
    (cofibrations PointedSimplicialSet.{u}).HasFunctorialFactorization pointedI.rlp := by
  let : pointedI.{u}.HasSmallObjectArgument.{u} := pointedI_smallObjectArgument
  rw [← pointedI_leftClass]
  infer_instance

/-- Pointed horn generation detects anodyne underlying maps. This does not
identify them with trivial cofibrations until the weak-equivalence input is supplied. -/
lemma pointedJ_leftClass : pointedJ.{u}.rlp.llp =
    SSet.anodyneExtensions.inverseImage PointedSimplicialSet.forget := by
  rw [pointedGenerators_rlp]
  change (J.{u}.rlp.under (X := 𝟙_ SSet.{u})).llp =
    J.{u}.rlp.llp.under
  have hret : (J.{u}.rlp.llp.under (X := 𝟙_ SSet.{u})).IsStableUnderRetracts := by
    rw [MorphismProperty.under_eq_inverseImage]
    infer_instance
  let : (J.{u}.rlp.llp.under (X := 𝟙_ SSet.{u})).IsStableUnderRetracts := hret
  apply MorphismProperty.llp_eq_of_le_llp_of_hasFactorization_of_isStableUnderRetracts
  intro A B i hi X Y p hp
  let : HasLiftingProperty i.right p.right := hi _ hp
  exact HasLiftingProperty.under i p

/-- The pointed anodyne/Kan-fibration pair is a concrete weak factorization system. -/
lemma pointedJ_weakFactorizationSystem :
    MorphismProperty.IsWeakFactorizationSystem
      (SSet.anodyneExtensions.inverseImage PointedSimplicialSet.forget.{u})
      (fibrations PointedSimplicialSet.{u}) := by
  let : pointedJ.{u}.HasSmallObjectArgument.{u} := pointedJ_smallObjectArgument
  rw [← pointedJ_leftClass, ← pointedJ_rlp]
  infer_instance

lemma pointedJ_functorialFactorization :
    (SSet.anodyneExtensions.inverseImage PointedSimplicialSet.forget.{u}).HasFunctorialFactorization
      (fibrations PointedSimplicialSet.{u}) := by
  let : pointedJ.{u}.HasSmallObjectArgument.{u} := pointedJ_smallObjectArgument
  rw [← pointedJ_leftClass, ← pointedJ_rlp]
  infer_instance

end SerrePositivity.SimplicialModelInputs
