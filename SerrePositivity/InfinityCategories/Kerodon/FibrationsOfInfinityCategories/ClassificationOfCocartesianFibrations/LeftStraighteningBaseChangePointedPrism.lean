module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RelativeFunctorIsoImageTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningEdgeLiftFamily

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningNativeCoefficientComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningTransportBaseChangeNormalization
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramOppositeValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramOppositeHomIntervalNatural

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexUnderNativeBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramNaturalTransformationComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramNaturalTransformationPrecomposition

public meta import SerrePositivity.Util.Citation

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportRepresentationUnstraighteningComparison

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffoldBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffoldComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseAscent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PrecompositionCriterion
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.StrictKanPointedComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCosliceBaseNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChangePullbackData
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldCoherentComparisonRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StraighteningReconstructionRepresentationComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SimplexUnderJointComposition

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChangeVertices

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeUnstraighteningHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoValue

/-!
概要：P3-C1Pの証明分割。scaffold上の指定pointed比較を全空間と指定辺へ移す。
方針：既存の前合成の充満忠実性・像の回収・辺代表の持ち上げを順に使う。
規約：HTT §3.3.2、Kerodon Corollary 5.6.0.6（Tag 028T）の構成の照合に使う法則。
  この補助部分だけでは、元のscaffold上のpointed比較の存在は結論していない。
使われ方：5∞-1のP3-C1P。元のνの辺代表を変えず、端点と射影を厳密に保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma pointedComparisonIsoOfRestriction {A Z X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (i : Z ⟶ A) (hi : IsPrecompositionEquivalence i) (q : X ⟶ Y)
    {f g : A ⟶ X} (d : FunctorIso (f ≫ q) (g ≫ q))
    (e : FunctorIso (i ≫ f) (i ≫ g))
    (h : e.postcomp q = d.precomp i) :
    ∃ a : FunctorIso f g, a.precomp i = e ∧ a.postcomp q = d := by
  let ff := (hi X).isFullyFaithful
  let a : FunctorIso f g := ff.preimageVertexIso
    (x := functorVertex f) (y := functorVertex g) e
  have hm : VertexIso.map a ((pre i).app X) = e :=
    ff.preimageVertexIso_map (x := functorVertex f) (y := functorVertex g) e
  have ha : a.precomp i = e := by
    exact eq_of_heq ((functorIsoPrecomp_heq_map a i).trans (heq_of_eq hm))
  refine ⟨a, ha, ?_⟩
  apply functorIso_precomp_injective i (hi Y).isFullyFaithful
  rw [← functorIso_precomp_postcomp, ha, h]

private lemma pointedPrismOfRestriction {A B Z : SSet.{u+1}} (p : A ⟶ B)
    (i : Z ⟶ A) (hi : IsPrecompositionEquivalence i)
    {F G : B ⟶ SpaceInfinity.{u}} (ν : FunctorIso F G)
    {f g : A ⟶ PointedSpaceInfinity.{u}}
    (hf : f ≫ pointedSpaceProjection = p ≫ F)
    (hg : g ≫ pointedSpaceProjection = p ≫ G)
    (e : FunctorIso (i ≫ f) (i ≫ g))
    (h : e.postcomp pointedSpaceProjection =
      (functorIsoOfEq (ν.precomp p) hf.symm hg.symm).precomp i) :
    let r := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
    ∃ W : (Δ[1] : SSet.{u+1}) ⊗ A ⟶ PointedSpaceInfinity.{u},
      prismEndpoint 0 A ≫ W = f ∧ prismEndpoint 1 A ≫ W = g ∧
      W ≫ pointedSpaceProjection = (Δ[1] ◁ p) ≫ functorEdgePrism r := by
  dsimp only
  obtain ⟨a, _, haq⟩ := pointedComparisonIsoOfRestriction i hi pointedSpaceProjection
    (functorIsoOfEq (ν.precomp p) hf.symm hg.symm) e h
  have hn : functorIsoOfEq (a.postcomp pointedSpaceProjection) hf hg = ν.precomp p := by
    exact eq_of_heq ((functorIsoOfEq_heq _ hf hg).trans
      ((heq_of_eq haq).trans (functorIsoOfEq_heq _ hf.symm hg.symm)))
  let r := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  let rp := r.map ((truncation 2).map ((pre p).app SpaceInfinity.{u}))
  have hrp : Truncated.HomotopyCategory.homMk rp = (ν.precomp p).hom := by
    change (SSet.mapHomotopyCategory ((pre p).app SpaceInfinity.{u})).map
      (Truncated.HomotopyCategory.homMk r) = _
    rw [functorHomHomotopy_hom, functorIso_precomp_hom]
  obtain ⟨l, hl, _⟩ := functorIso_exists_edge_representative_over pointedSpaceProjection
    a (ν.precomp p) hf hg hn rp hrp
  refine ⟨functorEdgePrism l, functorEdgePrism_zero _, functorEdgePrism_one _, ?_⟩
  have hx : SSet.yonedaEquiv.symm l.edge ≫ (ihom A).map pointedSpaceProjection =
      SSet.yonedaEquiv.symm r.edge ≫ (pre p).app SpaceInfinity.{u} := by
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm hl
  change functorFamilyPrism (SSet.yonedaEquiv.symm l.edge) ≫ pointedSpaceProjection = _
  rw [← functorFamilyPrism_post, hx, functorFamilyPrism_pre]
  rfl


open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

private lemma oppositePointWeightedBase {C D : Type u} [SmallCategory C] [SmallCategory D]
    (H : D ⥤ C) (F : C ⥤ KanObject.{u}) :
    weightedNerveBaseMap H (F ⋙ kanObjectForget) ≫ (oppositePointHomWeightedIso F).inv =
      (oppositePointHomWeightedIso (H ⋙ F)).inv ≫
        weightedNerveBaseMap H
          (simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

private lemma oppositeComparisonPointedBase {C D : Type u} [SmallCategory C] [SmallCategory D]
    (H : D ⥤ C) (F : C ⥤ KanObject.{u}) :
    oppositeKanUnstraighteningComparison (H ⋙ F) ≫
      pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve ((H ⋙ F) ⋙ kanObjectOpFunctor)) =
      (SSet.uliftFunctor.{u+1,u}).map (weightedNerveBaseMap H (F ⋙ kanObjectForget)) ≫
        oppositeKanUnstraighteningComparison F ≫
          pullback.fst pointedSpaceProjection
            (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) := by
  rw [oppositeKanUnstraighteningComparison, Category.assoc,
    strictKanUnstraighteningComparison_pointed]
  rw [oppositeKanUnstraighteningComparison, Category.assoc,
    strictKanUnstraighteningComparison_pointed]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

private def pullbackSectionsShift {E P B D : SSet.{u}} {J : Type u} [Category.{u} J]
    (p : E ⟶ B) [LeftFibration p] (r : P ⟶ D) [LeftFibration r]
    (t : P ⟶ E) (b : D ⟶ B) (hs : IsPullback t r p b) (A : Jᵒᵖ ⥤ Over D) :
    (relativeSectionEnrichedDiagram A).evaluate (leftFibrationObjectOf r) ⋙ kanObjectForget ≅
      (relativeSectionEnrichedDiagram (A ⋙ Over.map b)).evaluate
        (leftFibrationObjectOf p) ⋙ kanObjectForget := by
  refine NatIso.ofComponents (fun j => relativeFunctorIsPullbackIso hs
    (A.obj (Opposite.op j)).hom ((A.obj (Opposite.op j)).hom ≫ b) rfl) ?_
  intro i j f
  change relativeFunctorOverPre r (A.map f.op) ≫
      relativeFunctorIsPullbackForward hs (A.obj (Opposite.op j)).hom
        ((A.obj (Opposite.op j)).hom ≫ b) rfl =
    relativeFunctorIsPullbackForward hs (A.obj (Opposite.op i)).hom
        ((A.obj (Opposite.op i)).hom ≫ b) rfl ≫
      relativeFunctorOverPre p ((Over.map b).map (A.map f.op))
  apply relativeFunctorUncurry_injective
  have hpre := relativeFunctorOverPre_uncurry r (A.map f.op) (𝟙 _)
  have hfor := relativeFunctorIsPullbackForward_uncurry hs
    (A.obj (Opposite.op i)).hom ((A.obj (Opposite.op i)).hom ≫ b) rfl (𝟙 _)
  simp only [Category.id_comp] at hpre hfor
  have hright := relativeFunctorOverPre_uncurry p ((Over.map b).map (A.map f.op))
    (relativeFunctorIsPullbackForward hs (A.obj (Opposite.op i)).hom
      ((A.obj (Opposite.op i)).hom ≫ b) rfl)
  rw [relativeFunctorIsPullbackForward_uncurry, hright, hpre, hfor]
  exact Category.assoc _ _ _

private def underBaseChange {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) :
    strictTransportDomains D ⋙ Over.map (nerveMap H) ⟶
      H.op ⋙ strictTransportDomains C where
  app s := Over.homMk (nerveMap (Under.post (X := s.unop) H)) (by
    have h₁ : nerveMap (Under.post (X := s.unop) H ⋙ Under.forget (H.obj s.unop)) =
        nerveMap (Under.post (X := s.unop) H) ≫ nerveMap (Under.forget (H.obj s.unop)) :=
      nerveFunctor.map_comp (Under.post (X := s.unop) H).toCatHom
        (Under.forget (H.obj s.unop)).toCatHom
    have h₂ : nerveMap (Under.forget s.unop ⋙ H) =
        nerveMap (Under.forget s.unop) ≫ nerveMap H :=
      nerveFunctor.map_comp (Under.forget s.unop).toCatHom H.toCatHom
    have hF : Under.post (X := s.unop) H ⋙ Under.forget (H.obj s.unop) =
        Under.forget s.unop ⋙ H := rfl
    change nerveMap (Under.post (X := s.unop) H) ≫
      nerveMap (Under.forget (H.obj s.unop)) =
      nerveMap (Under.forget s.unop) ≫ nerveMap H
    rw [← h₁, hF, h₂])
  naturality {s t} f := by
    apply Over.OverMorphism.ext
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro τ
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      change Under.mk (H.map (f.unop ≫ (τ.obj i).hom)) =
        Under.mk (H.map f.unop ≫ H.map (τ.obj i).hom)
      rw [H.map_comp]
    case h_map =>
      intro i j g
      apply StructuredArrow.hom_ext
      simp only [Under.comp_right, Under.eqToHom_right, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      rfl

private def pullbackStrictComparison {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    H ⋙ leftStrictTransportDiagram p ⟶ leftStrictTransportDiagram r := by
  let η := relativeSectionDiagramComparison (underBaseChange H) (leftFibrationObjectOf p)
  let e := pullbackSectionsShift p r t (nerveMap H) hs (strictTransportDomains D)
  exact η ≫ e.inv

private lemma underRestrictionEq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] (H : D ⥤ C) (j : D) :
    IsQCatEquivalence (relativeFunctorOverPre p ((underBaseChange H).app (Opposite.op j))) := by
  let a := (strictTransportDomains D ⋙ Over.map (nerveMap H)).obj (Opposite.op j)
  let b := (H.op ⋙ strictTransportDomains C).obj (Opposite.op j)
  let f : a ⟶ b := (underBaseChange H).app (Opposite.op j)
  let z := nervePoint (Under.mk (𝟙 j))
  let c := Over.mk (z ≫ a.hom)
  let u : c ⟶ a := Over.homMk z rfl
  let v : c ⟶ b := u ≫ f
  have hv : v.left = nervePoint (Under.mk (𝟙 (H.obj j))) := by
    change nervePoint (Under.mk (𝟙 j)) ≫ nerveMap (Under.post (X := j) H) = _
    rw [nervePoint, nervePoint, SSet.yonedaEquiv_symm_comp]
    congr 1
    apply (nerveEquiv (C := Under (H.obj j))).injective
    change Under.mk (H.map (𝟙 j)) = Under.mk (𝟙 (H.obj j))
    rw [H.map_id]
  exact relativeFunctorOverPre_isQCatEquivalence_of_initialComparison p f u v
    (nervePoint_leftAnodyne Under.mkIdInitial)
    (by rw [hv]; exact nervePoint_leftAnodyne Under.mkIdInitial) rfl

private lemma pullbackStrictComparison_app {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) (j : D) :
    (pullbackStrictComparison p r t H hs).app j =
      relativeFunctorOverPre p ((underBaseChange H).app (Opposite.op j)) ≫
        (relativeFunctorIsPullbackIso hs (nerveMap (Under.forget j))
          (nerveMap (Under.forget j) ≫ nerveMap H) rfl).inv := rfl

private lemma pullbackStrictComparison_eq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) (j : D) :
    letI : KanComplex ((H ⋙ leftStrictTransportDiagram p).obj j) :=
      leftStrictTransport_kanComplex p (H.obj j)
    letI : KanComplex ((leftStrictTransportDiagram r).obj j) :=
      leftStrictTransport_kanComplex r j
    IsQCatEquivalence ((pullbackStrictComparison p r t H hs).app j) := by
  rw [pullbackStrictComparison_app]
  exact (underRestrictionEq p H j).comp
    (qCatEquivalenceOfIso (relativeFunctorIsPullbackIso hs (nerveMap (Under.forget j))
      (nerveMap (Under.forget j) ≫ nerveMap H) rfl).symm).isQCatEquivalence


open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

private lemma precompAsEmptyLocalization {A B : SSet.{u}} (f : A ⟶ B)
    (h : IsPrecompositionEquivalence f) : IsLocalization f ∅ := by
  apply isLocalization_of_fullyFaithful_extensions f ∅ (by intro s hs; cases hs)
  · intro Y hY
    exact (h Y).isFullyFaithful
  · intro Y hY F hF
    obtain ⟨v, ⟨e⟩⟩ := (h Y).choose.isEssentiallySurjective (functorVertex F)
    obtain ⟨G, rfl⟩ := (functorVertexEquiv B Y).surjective v
    exact ⟨G, ⟨e⟩⟩

private lemma emptyInvertingEquivalence {A E : SSet.{u}} [Quasicategory E] :
    IsQCatEquivalence (invertingFunctors A E ∅).ι := by
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · exact isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  · intro v
    refine ⟨⟨v, ?_⟩, ⟨Iso.refl _⟩⟩
    intro w s hs
    cases hs

private lemma uliftPrecomp {A B : SSet.{u}} (f : A ⟶ B)
    (h : IsPrecompositionEquivalence f) :
    IsPrecompositionEquivalence ((SSet.uliftFunctor.{u+1,u}).map f) := by
  let U := SSet.uliftFunctor.{u+1,u}
  have hL := precompAsEmptyLocalization f h
  have hu : IsLocalization (U.map f) ∅ := by
    have hh : IsLocalization (U.map f) (ULift.up.{u+1,u} '' (∅ : Set (A _⦋1⦌))) := hL.ulift
    simpa only [Set.image_empty] using hh
  intro Y hY
  rw [← localizationPrecomposition_ι (U.map f) ∅ hu.choose Y]
  exact (hu.choose_spec Y).comp emptyInvertingEquivalence

private def scaffoldPullbackData {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    { l : simplicialReplacement (H ⋙ leftStrictTransportDiagram p) ⟶ P //
      l ≫ t = simplicialReplacementBaseMap H (leftStrictTransportDiagram p) ≫
        universalScaffold p ∧
      l ≫ r = simplicialReplacementProjection (H ⋙ leftStrictTransportDiagram p) ∧
      IsPrecompositionEquivalence l } := by
  let F := leftStrictTransportDiagram p
  haveI : ∀ c, KanComplex (F.obj c) := fun c => leftStrictTransport_kanComplex p c
  haveI : ∀ c, KanComplex ((H ⋙ F).obj c) :=
    fun c => leftStrictTransport_kanComplex p (H.obj c)
  let h := universalScaffold_projection p
  have hsc : IsLeftScaffold (pullback.snd p (nerveMap H)) (H ⋙ F)
      (leftScaffoldBaseChange p F (universalScaffold p) h H) := by
    obtain ⟨h', hsc'⟩ := (universalScaffold_isLeftScaffold p).baseChange H
    exact hsc'
  let l₀ := leftScaffoldBaseChange p F (universalScaffold p) h H
  let l := l₀ ≫ hs.isoPullback.inv
  refine ⟨l, ?_, ?_, ?_⟩
  · dsimp only [l]
    rw [Category.assoc, hs.isoPullback_inv_fst]
    exact pullback.lift_fst _ _ _
  · dsimp only [l]
    rw [Category.assoc, hs.isoPullback_inv_snd]
    exact leftScaffoldBaseChange_projection p F (universalScaffold p) h H
  · exact hsc.isPrecompositionEquivalence.comp (isPrecompositionEquivalence_of_iso hs.isoPullback.symm)
private lemma pullbackStrictComparison_uncurry {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P T : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) (j : D)
    (τ : T ⟶ (H ⋙ leftStrictTransportDiagram p).obj j) :
    relativeFunctorUncurry (τ ≫ (pullbackStrictComparison p r t H hs).app j) ≫ t =
      (nerveMap (Under.post H) ▷ T) ≫ relativeFunctorUncurry τ := by
  change T ⟶ relativeFunctorSpace p (nerveMap (Under.forget (H.obj j))) at τ
  rw [pullbackStrictComparison_app, ← Category.assoc]
  change relativeFunctorUncurry ((τ ≫ relativeFunctorOverPre p
    ((underBaseChange H).app (Opposite.op j))) ≫
    relativeFunctorIsPullbackBackward hs (nerveMap (Under.forget j))
      (nerveMap (Under.forget j) ≫ nerveMap H) rfl) ≫ t = _
  have hb := relativeFunctorIsPullbackBackward_uncurry hs (nerveMap (Under.forget j))
    (nerveMap (Under.forget j) ≫ nerveMap H) rfl
    (τ ≫ relativeFunctorOverPre p ((underBaseChange H).app (Opposite.op j)))
  have hpre := relativeFunctorOverPre_uncurry p ((underBaseChange H).app (Opposite.op j)) τ
  exact (congrArg (fun z => z ≫ t) hb).trans ((hs.lift_fst _ _ _).trans hpre)

private lemma scaffoldUnderChain_post {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) {n : ℕ} (σ : ComposableArrows D n) :
    scaffoldUnderChain σ ⋙ Under.post H = scaffoldUnderChain (σ ⋙ H) := by
  refine CategoryTheory.Functor.ext (fun i => rfl) ?_
  intro i j f
  apply StructuredArrow.hom_ext
  simp only [eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rfl

private lemma pullbackScaffold_naturality {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    simplicialReplacementMap (pullbackStrictComparison p r t H hs) ≫ universalScaffold r ≫ t =
      simplicialReplacementBaseMap H (leftStrictTransportDiagram p) ≫ universalScaffold p := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  change t.app d (SSet.yonedaEquiv (universalScaffoldSimplex r
      ⟨s.1, s.2 ≫ (pullbackStrictComparison p r t H hs).app (s.1.obj 0)⟩)) =
    SSet.yonedaEquiv (universalScaffoldSimplex p ⟨s.1 ⋙ H, s.2⟩)
  rw [← SSet.yonedaEquiv_comp]
  congr 1
  simp only [universalScaffoldSimplex,
    Category.assoc, pullbackStrictComparison_uncurry]
  have hc : SSet.yonedaEquiv.symm (scaffoldUnderChain s.1) ≫ nerveMap (Under.post H) =
      SSet.yonedaEquiv.symm (scaffoldUnderChain (s.1 ⋙ H)) := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (scaffoldUnderChain_post H s.1)
  rw [← Category.assoc, CartesianMonoidalCategory.lift_whiskerRight, hc]
  rfl

private lemma scaffoldPullbackData_eq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {E P : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (r : P ⟶ nerve D) [LeftFibration r] (t : P ⟶ E) (H : D ⥤ C)
    (hs : IsPullback t r p (nerveMap H)) :
    (scaffoldPullbackData p r t H hs).val =
      simplicialReplacementMap (pullbackStrictComparison p r t H hs) ≫ universalScaffold r := by
  apply hs.hom_ext
  · exact (scaffoldPullbackData p r t H hs).property.1.trans
      (pullbackScaffold_naturality p r t H hs).symm
  · rw [Category.assoc, universalScaffold_projection, simplicialReplacementMap_projection]
    exact (scaffoldPullbackData p r t H hs).property.2.1

private lemma scaffoldRelativeIso {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    let U := SSet.uliftFunctor.{u+1,u}
    let q := leftUnstraighteningProjection (leftCoherentTransport p)
    let f := U.map (universalScaffold p) ≫ scaffoldCoherentComparison p
    let g := U.map (tautScaffold (leftStrictTransportDiagram p)) ≫ leftCoherentTransportComparison p
    let b := U.map (simplicialReplacementProjection (leftStrictTransportDiagram p))
    ∃ (hf : f ≫ q = b) (hg : g ≫ q = b),
      Nonempty (VertexIso (relativeFunctorVertex q b f hf) (relativeFunctorVertex q b g hg)) := by
  dsimp only
  let U := SSet.uliftFunctor.{u+1,u}
  let s := scaffoldTransportComparisonSpan p
  let q := leftUnstraighteningProjection (leftCoherentTransport p)
  let f := U.map (universalScaffold p) ≫ scaffoldCoherentComparison p
  let g := U.map (tautScaffold (leftStrictTransportDiagram p)) ≫ leftCoherentTransportComparison p
  let b := U.map (simplicialReplacementProjection (leftStrictTransportDiagram p))
  have hf : f ≫ q = b := by
    dsimp only [f,q,b]
    rw [Category.assoc, scaffoldCoherentComparison_projection, ← U.map_comp,
      universalScaffold_projection]
  have hg : g ≫ q = b := by
    dsimp only [g,q,b]
    rw [Category.assoc, leftCoherentTransportComparison_projection, ← U.map_comp]
    exact congrArg U.map (tautScaffold_projection (leftStrictTransportDiagram p))
  let j := U.map s.embedding
  have hj : j ≫ s.coherentBase = b := by
    change U.map s.embedding ≫ U.map s.projection = _
    rw [← U.map_comp, s.embedding_over]
  let v : Over.mk b ⟶ Over.mk s.coherentBase := Over.homMk j hj
  let pre := relativeFunctorOverPre q v
  let e := (scaffoldCoherentComparison_restrictionIso p).map pre
  have hL : pre.app _ ((relativeFunctorOverPre q
      (show Over.mk s.coherentBase ⟶ Over.mk (U.map p)
        from Over.homMk s.coherentSource s.coherentSource_over)).app _
          (relativeFunctorVertex q (U.map p) (scaffoldCoherentComparison p)
            (scaffoldCoherentComparison_projection p))) = relativeFunctorVertex q b f hf := by
    apply Subtype.ext
    change functorVertex (j ≫ (U.map s.source ≫ scaffoldCoherentComparison p)) = functorVertex f
    apply congrArg functorVertex
    dsimp only [j,f]
    rw [← Category.assoc, ← U.map_comp, s.source_restriction]
  have hR : pre.app _ (relativeFunctorVertex q s.coherentBase s.coherentTarget s.coherentTarget_over) =
      relativeFunctorVertex q b g hg := by
    apply Subtype.ext
    change functorVertex (j ≫ (U.map s.weighted ≫ leftCoherentTransportComparison p)) = functorVertex g
    apply congrArg functorVertex
    dsimp only [j,g]
    rw [← Category.assoc, ← U.map_comp, s.weighted_restriction]
  exact ⟨hf,hg,⟨(eqToIso (congrArg HomotopyCategory.mk hL)).symm ≪≫ e ≪≫
    eqToIso (congrArg HomotopyCategory.mk hR)⟩⟩

@[cite HTT "3.3.2" (partial := special) "通常の小さい底のscaffoldに沿う、同じ指定比較の相対pointed移送。"]
private lemma scaffoldPointedRelativeIso {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    let U := SSet.uliftFunctor.{u+1,u}
    let F := leftCoherentTransport p
    let f := U.map (universalScaffold p) ≫ (nerveLeftTransportRepresentation p).pointedMap
    let g := U.map (tautScaffold (leftStrictTransportDiagram p)) ≫
      leftCoherentTransportComparison p ≫ pullback.fst pointedSpaceProjection F
    let b := U.map (simplicialReplacementProjection (leftStrictTransportDiagram p)) ≫ F
    ∃ (hf : f ≫ pointedSpaceProjection = b) (hg : g ≫ pointedSpaceProjection = b),
      Nonempty (VertexIso (relativeFunctorVertex pointedSpaceProjection b f hf)
        (relativeFunctorVertex pointedSpaceProjection b g hg)) := by
  dsimp only
  let U := SSet.uliftFunctor.{u+1,u}
  let F := leftCoherentTransport p
  let q := leftUnstraighteningProjection F
  let a := U.map (simplicialReplacementProjection (leftStrictTransportDiagram p))
  let f₀ := U.map (universalScaffold p) ≫ scaffoldCoherentComparison p
  let g₀ := U.map (tautScaffold (leftStrictTransportDiagram p)) ≫ leftCoherentTransportComparison p
  obtain ⟨hf₀,hg₀,⟨e⟩⟩ := scaffoldRelativeIso p
  let m := relativeFunctorBaseChangeForward pointedSpaceProjection F a
  let f := f₀ ≫ pullback.fst pointedSpaceProjection F
  let g := g₀ ≫ pullback.fst pointedSpaceProjection F
  have hf : f ≫ pointedSpaceProjection = a ≫ F := by
    dsimp only [f]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun z => z ≫ F) hf₀
  have hg : g ≫ pointedSpaceProjection = a ≫ F := by
    dsimp only [g]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun z => z ≫ F) hg₀
  have hL : m.app _ (relativeFunctorVertex q a f₀ hf₀) =
      relativeFunctorVertex pointedSpaceProjection (a ≫ F) f hf := by
    exact relativeFunctorBaseChangeForward_vertex pointedSpaceProjection F a f₀ hf₀
  have hR : m.app _ (relativeFunctorVertex q a g₀ hg₀) =
      relativeFunctorVertex pointedSpaceProjection (a ≫ F) g hg := by
    exact relativeFunctorBaseChangeForward_vertex pointedSpaceProjection F a g₀ hg₀
  have e' := (eqToIso (congrArg HomotopyCategory.mk hL)).symm ≪≫ e.map m ≪≫
    eqToIso (congrArg HomotopyCategory.mk hR)
  have hfa : f = U.map (universalScaffold p) ≫
      (nerveLeftTransportRepresentation p).pointedMap := by
    dsimp only [f,f₀]
    exact Category.assoc _ _ _
  have hga : g = U.map (tautScaffold (leftStrictTransportDiagram p)) ≫
      leftCoherentTransportComparison p ≫ pullback.fst pointedSpaceProjection F :=
    Category.assoc _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← hfa]; exact hf
  · rw [← hga]; exact hg
  · cases hfa
    cases hga
    exact ⟨e'⟩
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

private def naturalHomVertex {I : Type u} [SmallCategory I] (F G : KanDiagramObject I)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    ((SSet.uliftFunctor.{u+1,u}).obj (edgewiseSubdivision (SimplicialCategory.sHom F G))) _⦋0⦌ :=
  ULift.up (SSet.const (strictDiagramMappingVertex η))

private lemma oppositeHomLeft_at_natural {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    let U := SSet.uliftFunctor.{u+1,u}
    let q := leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))
    let a := U.map (weightedNerveProjection (F.val ⋙ kanObjectForget))
    let f := U.map (weightedNerveMap η) ≫ oppositeKanUnstraighteningComparison G.val
    ∃ hf : f ≫ q = a,
      (oppositeUnstraighteningHomLeft F G).app _ (naturalHomVertex F G η) =
        relativeFunctorVertex q a f hf := by
  dsimp only
  let U := SSet.uliftFunctor.{u+1,u}
  have hf : (U.map (weightedNerveMap η) ≫ oppositeKanUnstraighteningComparison G.val) ≫
      leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) =
      U.map (weightedNerveProjection (F.val ⋙ kanObjectForget)) := by
    rw [Category.assoc, oppositeKanUnstraighteningComparison_projection, ← U.map_comp,
      weightedNerveMap_projection]
  refine ⟨hf, ?_⟩
  apply Subtype.ext
  rfl

@[cite HTT "3.3.2" (partial := special) "通常の小さい添字圏で、元の全Homの反転比較を指定自然変換で評価する照合。"]
private lemma oppositeHomComparison_at_natural {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    let U := SSet.uliftFunctor.{u+1,u}
    let F' := kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)
    let G' := kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)
    let y := (kanDiagramOppositeHomInterval F G).app _ (naturalHomVertex F G η)
    let m := CartesianMonoidalCategory.lift (𝟙 (leftUnstraightening F')) (SSet.const y) ≫
      leftUnstraighteningMappingFamily F' G'
    let g := oppositeKanUnstraighteningComparison F.val ≫ m
    let f := U.map (weightedNerveMap η) ≫ oppositeKanUnstraighteningComparison G.val
    let a := U.map (weightedNerveProjection (F.val ⋙ kanObjectForget))
    let q := leftUnstraighteningProjection G'
    ∃ (hg : g ≫ q = a) (hf : f ≫ q = a),
      Nonempty (VertexIso (relativeFunctorVertex q a g hg) (relativeFunctorVertex q a f hf)) := by
  dsimp only
  let U := SSet.uliftFunctor.{u+1,u}
  let F' := kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)
  let G' := kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)
  let x := naturalHomVertex F G η
  let y := (kanDiagramOppositeHomInterval F G).app _ x
  let m := CartesianMonoidalCategory.lift (𝟙 (leftUnstraightening F')) (SSet.const y) ≫
    leftUnstraighteningMappingFamily F' G'
  have hm : m ≫ leftUnstraighteningProjection G' = leftUnstraighteningProjection F' := by
    have hp : leftUnstraighteningMappingFamily F' G' ≫ leftUnstraighteningProjection G' =
        CartesianMonoidalCategory.fst _ _ ≫ leftUnstraighteningProjection F' := pullback.lift_snd _ _ _
    dsimp only [m]
    rw [Category.assoc,hp,← Category.assoc,CartesianMonoidalCategory.lift_fst,Category.id_comp]
  have hg : (oppositeKanUnstraighteningComparison F.val ≫ m) ≫ leftUnstraighteningProjection G' =
      U.map (weightedNerveProjection (F.val ⋙ kanObjectForget)) := by
    rw [Category.assoc,hm]
    exact oppositeKanUnstraighteningComparison_projection F.val
  obtain ⟨hf,hL⟩ := oppositeHomLeft_at_natural F G η
  have hR : (oppositeUnstraighteningHomRight F G).app _ x =
      relativeFunctorVertex (leftUnstraighteningProjection G')
        (U.map (weightedNerveProjection (F.val ⋙ kanObjectForget)))
        (oppositeKanUnstraighteningComparison F.val ≫ m) hg := by
    change (relativeFunctorOverPre (leftUnstraighteningProjection G')
      (oppositeKanUnstraighteningOverMap F)).app _
        ((leftUnstraighteningMappingSpaceMap F' G').app _ y) = _
    rw [leftUnstraighteningMappingSpaceMap_vertex]
    exact relativeFunctorOverPre_vertex (leftUnstraighteningProjection G')
      (oppositeKanUnstraighteningOverMap F) m hm
  have e := functorIsoValue (oppositeUnstraighteningHomComparisonIso F G) x
  exact ⟨hg,hf,⟨(eqToIso (congrArg HomotopyCategory.mk hR)).symm ≪≫ e ≪≫
    eqToIso (congrArg HomotopyCategory.mk hL)⟩⟩
private lemma pointedIsoOfProjectedPrism {A : SSet.{u+1}}
    {f g : A ⟶ PointedSpaceInfinity.{u}}
    (d : FunctorIso (f ≫ pointedSpaceProjection) (g ≫ pointedSpaceProjection))
    (r : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom A).obj SpaceInfinity.{u}))
      (functorVertex (f ≫ pointedSpaceProjection)) (functorVertex (g ≫ pointedSpaceProjection)))
    (hr : SSet.Truncated.HomotopyCategory.homMk r = d.hom)
    (W : (Δ[1] : SSet.{u+1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (h₀ : prismEndpoint 0 A ≫ W = f) (h₁ : prismEndpoint 1 A ≫ W = g)
    (hp : W ≫ pointedSpaceProjection = functorEdgePrism r) :
    ∃ a : FunctorIso f g, a.postcomp pointedSpaceProjection = d := by
  let H : SSet.Homotopy f g := {
    h := (β_ A (Δ[1] : SSet.{u+1})).hom ≫ W
    h₀ := by change prismEndpoint 0 A ≫ W = f; exact h₀
    h₁ := by change prismEndpoint 1 A ≫ W = g; exact h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  let l := functorEdgeOfSimplicialHomotopy H
  have hl : functorFamilyPrism (SSet.yonedaEquiv.symm l.edge) = W := by
    change (β_ (Δ[1] : SSet.{u+1}) A).hom ≫
      uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = W
    rw [Equiv.symm_apply_apply, uncurry_curry]
    change (β_ (Δ[1] : SSet.{u+1}) A).hom ≫
      (β_ A (Δ[1] : SSet.{u+1})).hom ≫ W = W
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hm : l.map ((truncation 2).map ((ihom A).map pointedSpaceProjection)) = r := by
    apply SSet.Truncated.Edge.ext
    apply (SSet.yonedaEquiv (X := ((ihom A).obj SpaceInfinity.{u})) (n := ⦋1⦌)).symm.injective
    change SSet.yonedaEquiv.symm (((ihom A).map pointedSpaceProjection).app
      (Opposite.op ⦋1⦌) l.edge) = SSet.yonedaEquiv.symm r.edge
    rw [← SSet.yonedaEquiv_symm_comp]
    apply functorFamilyPrism_injective (Δ[1] : SSet.{u+1}) A SpaceInfinity.{u}
    rw [functorFamilyPrism_post]
    exact (congrArg (fun z => z ≫ pointedSpaceProjection) hl).trans hp
  have he : IsInvertibleEdge r := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk r)
    rw [hr]
    infer_instance
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk l) :=
    leftFibration_reflects_invertibleEdge ((ihom A).map pointedSpaceProjection) l
      (by rw [hm]; exact he)
  refine ⟨asIso (SSet.Truncated.HomotopyCategory.homMk l), ?_⟩
  apply Iso.ext
  rw [functorIso_postcomp_hom]
  change SSet.Truncated.HomotopyCategory.homMk
    (l.map ((truncation 2).map ((ihom A).map pointedSpaceProjection))) = d.hom
  rw [hm,hr]


/-- 指定pullbackの二射影による、元の相対切断の底変換の長方形。
HTT §3.3.2・Kerodon Tag 028Tの指定構成の、この単体圏模型での特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "初頂点pullbackの指定二座標と相対切断の底変換の合成則。"]
private lemma leftStraighteningBaseChange_native_pullback_square :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    Functor.whiskerLeft H
      ((relativeSectionBaseChangeComparison lB (strictTransportDomains (TransportSimplexCategory B))).app
        (leftFibrationObjectOf p)) ≫
      relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k)
        (leftFibrationObjectOf p) =
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1 ≫
      (relativeSectionBaseChangeComparison lD (strictTransportDomains (TransportSimplexCategory D))).app
        (leftFibrationObjectOf q) ≫
      (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app
        (leftFibrationObjectOf p) := by
  intro E B D hB hD p hp k
  dsimp only
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let α := pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  apply NatTrans.ext
  funext j
  let aB := nerveMap (Under.forget (H.obj j))
  let aD := nerveMap (Under.forget j)
  let f := (transportSimplexUnderBaseChangeTransformation k).app (Opposite.op j)
  change relativeFunctorBaseChangeForward p lB aB ≫ relativeFunctorOverPre p f =
    α.app j ≫ relativeFunctorBaseChangeForward q lD aD ≫
      relativeFunctorBaseChangeForward p k (aD ≫ lD)
  apply relativeFunctorUncurry_injective p ((aD ≫ lD) ≫ k)
  have hb := relativeFunctorBaseChangeForward_uncurry p lB aB (𝟙 _)
  simp only [Category.id_comp] at hb
  have hpre := relativeFunctorOverPre_uncurry p f
    (relativeFunctorBaseChangeForward p lB aB)
  have hα := pullbackStrictComparison_uncurry p₀ r d.val H d.property.2.2.1 j (𝟙 _)
  simp only [Category.id_comp] at hα
  have hd : relativeFunctorUncurry (α.app j) ≫
      pullback.fst q lD ≫ pullback.fst p k =
      ((nerveMap (Under.post H)) ▷ relativeFunctorSpace p₀ aB) ≫
        relativeFunctorUncurry (𝟙 _) ≫ pullback.fst p lB := by
    calc
      _ = (relativeFunctorUncurry (α.app j) ≫ d.val) ≫ pullback.fst p lB := by
        rw [Category.assoc, d.property.1]
      _ = _ := congrArg (fun z => z ≫ pullback.fst p lB) hα
  have hrhs : relativeFunctorUncurry
      (α.app j ≫ relativeFunctorBaseChangeForward q lD aD ≫
        relativeFunctorBaseChangeForward p k (aD ≫ lD)) =
      relativeFunctorUncurry (α.app j) ≫ pullback.fst q lD ≫ pullback.fst p k := by
    rw [← Category.assoc, relativeFunctorBaseChangeForward_uncurry,
      relativeFunctorBaseChangeForward_uncurry, Category.assoc]
  rw [hpre, hb, hrhs]
  have hf : f.left = nerveMap (Under.post H) := rfl
  rw [hf]
  simpa only [Category.assoc] using hd.symm

private def nativeRectangleHom {J : Type u} [SmallCategory J]
    (F G : KanDiagramObject J) (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget) :
    FunctorHom (kanDiagramCoherentNerve F.val) (kanDiagramCoherentNerve G.val) :=
  Truncated.HomotopyCategory.homMk
    (kanDiagramNaturalTransformationEdge (F := F) (G := G) η).toTruncated

private lemma nativeRectangleHom_comp {J : Type u} [SmallCategory J]
    (F G K : KanDiagramObject J)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (θ : G.val ⋙ kanObjectForget ⟶ K.val ⋙ kanObjectForget) :
    nativeRectangleHom F K (η ≫ θ) = nativeRectangleHom F G η ≫ nativeRectangleHom G K θ :=
  kanDiagramNaturalTransformationHom_comp η θ

private lemma nativeRectangleHom_precomp {I J : Type u} [SmallCategory I] [SmallCategory J]
    (H : I ⥤ J) (F G : KanDiagramObject J)
    (η : F.val ⋙ kanObjectForget ⟶ G.val ⋙ kanObjectForget)
    (e : FunctorIso (kanDiagramCoherentNerve F.val) (kanDiagramCoherentNerve G.val))
    (he : e.hom = nativeRectangleHom F G η) :
    (diagramIsoCongr (kanDiagramCoherentNerve_precomp H F.val)
      (kanDiagramCoherentNerve_precomp H G.val)
      (e.precomp ((SSet.uliftFunctor.{u+1,u}).map (nerveMap H)))).hom =
      nativeRectangleHom ⟨H ⋙ F.val, trivial⟩ ⟨H ⋙ G.val, trivial⟩ (Functor.whiskerLeft H η) := by
  rw [diagramIsoCongr_hom, functorIsoPrecomp_hom, he]
  exact kanDiagramNaturalTransformationHom_precomp H η

private lemma nativeRectangle_cancel.{v, w} {C : Type v} [Category.{w} C]
    {a b c d e f g : C} (x : a ≅ b) (u : b ≅ c) (v : d ≅ c)
    (s : a ≅ e) (t : f ≅ e) (z : e ≅ g) (w : c ⟶ g) (r : d ⟶ f)
    (h₁ : x.hom ≫ u.hom ≫ w = s.hom ≫ z.hom)
    (h₂ : v.hom ≫ w = r ≫ t.hom ≫ z.hom) :
    (v ≪≫ u.symm ≪≫ x.symm ≪≫ s ≪≫ t.symm).hom = r := by
  apply (cancel_mono (t.hom ≫ z.hom)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [Iso.inv_hom_id_assoc, ← h₁]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h₂

/-- 反転前の指定係数の共役は、元のpullbackの自然変換の実現。
HTT §3.3.2・Kerodon Tag 028Tの構成の特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "指定長方形の実現と可逆な底変換の相殺。"]
private lemma leftStraighteningBaseChange_native_nonop_hom :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let t := U.map (nerveMap H)
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let Fh : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨leftStrictTransportFunctor r, trivial⟩
    let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
      pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let ν₀ := (FunctorIso.precomp
        (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
      (simplexSectionBaseChangeCoefficient p k).symm ≪≫
      nativeUnderCoefficientIso q ≪≫ (nativeBaseChangeCoefficientIso q).symm
    let hsrc : t ≫ leftStraighteningCandidate p₀ = kanDiagramCoherentNerve Fh.val := by
      change t ≫ kanDiagramCoherentNerve (leftStrictTransportFunctor p₀) =
        kanDiagramCoherentNerve (H ⋙ leftStrictTransportFunctor p₀)
      exact kanDiagramCoherentNerve_precomp H _
    ν₀.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
      Truncated.HomotopyCategory.homMk (kanDiagramNaturalTransformationEdge
        (F := Fh) (G := Fr) α).toTruncated := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let t := U.map (nerveMap H)
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let Fh : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) := ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let FP : KanDiagramObject (TransportSimplexCategory B) :=
    ⟨(relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate (leftFibrationObjectOf p), trivial⟩
  let UP : KanDiagramObject (TransportSimplexCategory B) :=
    ⟨(relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).evaluate (leftFibrationObjectOf p), trivial⟩
  let FPH : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ FP.val, trivial⟩
  let UPH : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ UP.val, trivial⟩
  let FQ : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨(relativeSectionEnrichedDiagram (transportSimplexDomainFunctor D)).evaluate (leftFibrationObjectOf q), trivial⟩
  let UQ : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨(relativeSectionEnrichedDiagram (transportSimplexUnderDomains D)).evaluate (leftFibrationObjectOf q), trivial⟩
  let Z : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨(relativeSectionEnrichedDiagram (transportSimplexUnderDomains D ⋙ Over.map k)).evaluate
      (leftFibrationObjectOf p), trivial⟩
  let cn := simplexSectionNativeBaseChange p k
  let un := Functor.whiskerLeft H ((nativeUnderJointComparison B).app (leftFibrationObjectOf p))
  let bn := Functor.whiskerLeft H
    ((relativeSectionBaseChangeComparison lB (strictTransportDomains (TransportSimplexCategory B))).app
      (leftFibrationObjectOf p))
  let uq := (nativeUnderJointComparison D).app (leftFibrationObjectOf q)
  let bq := (relativeSectionBaseChangeComparison lD (strictTransportDomains (TransportSimplexCategory D))).app
    (leftFibrationObjectOf q)
  let zn := (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D)).app (leftFibrationObjectOf p)
  let wn := relativeSectionDiagramComparison (transportSimplexUnderBaseChangeTransformation k) (leftFibrationObjectOf p)
  let hf := kanDiagramCoherentNerve_precomp H FP.val
  let hu := kanDiagramCoherentNerve_precomp H UP.val
  let hs := kanDiagramCoherentNerve_precomp H (leftStrictTransportFunctor p₀)
  let c := diagramIsoCongr rfl hf (simplexSectionBaseChangeCoefficient p k)
  let a := diagramIsoCongr hf hu ((nativeUnderCoefficientIso p).precomp t)
  let b := diagramIsoCongr hs hu ((nativeBaseChangeCoefficientIso p).precomp t)
  let a' := nativeUnderCoefficientIso q
  let b' := nativeBaseChangeCoefficientIso q
  let z := kanEnrichedRealizationValueIso (relativeSectionBaseChangeComparison k (transportSimplexUnderDomains D))
    (relativeSectionBaseChangeComparison_isQCatEquivalence k (transportSimplexUnderDomains D)) (leftFibrationObjectOf p)
  have hc : c.hom = nativeRectangleHom FQ FPH cn := by
    rw [diagramIsoCongr_hom]
    exact eq_of_heq ((kanFunctorHomCongr_heq rfl hf (simplexSectionBaseChangeCoefficient p k).hom).trans
      (simplexSectionBaseChangeCoefficient_native_hom p k))
  have ha : a.hom = nativeRectangleHom FPH UPH un := by
    apply nativeRectangleHom_precomp H FP UP
      ((nativeUnderJointComparison B).app (leftFibrationObjectOf p)) (nativeUnderCoefficientIso p)
    exact kanEnrichedRealizationValueIso_hom (nativeUnderJointComparison B)
      (fun j q => transportSimplexUnderPre_isQCatEquivalence q.val.hom j) (leftFibrationObjectOf p)
  have hb : b.hom = nativeRectangleHom Fh UPH bn := by
    apply nativeRectangleHom_precomp H ⟨leftStrictTransportFunctor p₀, trivial⟩ UP
      ((relativeSectionBaseChangeComparison lB (strictTransportDomains (TransportSimplexCategory B))).app
        (leftFibrationObjectOf p)) (nativeBaseChangeCoefficientIso p)
    exact kanEnrichedRealizationValueIso_hom
      (relativeSectionBaseChangeComparison lB (strictTransportDomains (TransportSimplexCategory B)))
      (relativeSectionBaseChangeComparison_isQCatEquivalence lB (strictTransportDomains (TransportSimplexCategory B)))
      (leftFibrationObjectOf p)
  have ha' : a'.hom = nativeRectangleHom FQ UQ uq :=
    kanEnrichedRealizationValueIso_hom (nativeUnderJointComparison D)
      (fun j q => transportSimplexUnderPre_isQCatEquivalence q.val.hom j) (leftFibrationObjectOf q)
  have hb' : b'.hom = nativeRectangleHom Fr UQ bq :=
    kanEnrichedRealizationValueIso_hom
      (relativeSectionBaseChangeComparison lD (strictTransportDomains (TransportSimplexCategory D)))
      (relativeSectionBaseChangeComparison_isQCatEquivalence lD (strictTransportDomains (TransportSimplexCategory D)))
      (leftFibrationObjectOf q)
  have hz : z.hom = nativeRectangleHom UQ Z zn :=
    kanEnrichedRealizationValueIso_hom _ _ _
  have upper : c.hom ≫ a.hom ≫ nativeRectangleHom UPH Z wn = a'.hom ≫ z.hom := by
    rw [hc, ha, ha', hz, ← nativeRectangleHom_comp, ← nativeRectangleHom_comp,
      ← nativeRectangleHom_comp]
    exact congrArg (nativeRectangleHom FQ Z) (simplexUnderNativeBaseChange_square p k)
  have lower : b.hom ≫ nativeRectangleHom UPH Z wn = nativeRectangleHom Fh Fr α ≫ b'.hom ≫ z.hom := by
    rw [hb, hb', hz, ← nativeRectangleHom_comp, ← nativeRectangleHom_comp,
      ← nativeRectangleHom_comp]
    exact congrArg (nativeRectangleHom Fh Z) (leftStraighteningBaseChange_native_pullback_square p k)
  have hrect : (b ≪≫ a.symm ≪≫ c.symm ≪≫ a' ≪≫ b'.symm).hom = nativeRectangleHom Fh Fr α :=
    nativeRectangle_cancel c a b a' b' z (nativeRectangleHom UPH Z wn) (nativeRectangleHom Fh Fr α) upper lower
  let ν₀ := (FunctorIso.precomp
      (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
    (simplexSectionBaseChangeCoefficient p k).symm ≪≫ nativeUnderCoefficientIso q ≪≫
      (nativeBaseChangeCoefficientIso q).symm
  have hnorm : diagramIsoCongr hs rfl ν₀ = b ≪≫ a.symm ≪≫ c.symm ≪≫ a' ≪≫ b'.symm := by
    dsimp only [ν₀]
    rw [functorIso_precomp_trans, functorIso_precomp_symm, Iso.trans_symm, Iso.symm_symm_eq]
    rw [diagramIsoCongr_trans hs hf rfl]
    rw [diagramIsoCongr_trans hs hu hf, diagramIsoCongr_symm hf hu]
    rw [diagramIsoCongr_trans hf rfl rfl, diagramIsoCongr_symm rfl hf]
    simp only [a, b, c, a', b', diagramIsoCongr, eqToIso_refl, Iso.refl_symm,
      Iso.refl_trans, Iso.trans_refl]
    exact Iso.trans_assoc _ _ _
  have hn : (diagramIsoCongr hs rfl ν₀).hom = nativeRectangleHom Fh Fr α := by
    rw [hnorm]
    exact hrect
  change ν₀.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hs) ≫
    nativeRectangleHom Fh Fr α
  rw [← hn]
  simp only [diagramIsoCongr, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (Category.id_comp ν₀.hom).symm

private lemma normalizedIsoHom_iff {A X : SSet.{u}} {f f' g : A ⟶ X}
    (hf : f = f') (e : FunctorIso f g) (a : FunctorHom f' g) :
    (diagramIsoCongr hf rfl e).hom = a ↔
      e.hom = eqToHom (congrArg (fun h => HomotopyCategory.mk (functorVertex h)) hf) ≫ a := by
  subst f'
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans,
    Iso.trans_refl, eqToHom_refl, Category.id_comp]

private lemma normalizedIso_rfl {A X : SSet.{u}} {f g : A ⟶ X} (e : FunctorIso f g) :
    diagramIsoCongr rfl rfl e = e := by
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

private lemma nativeTwistInverseChain {K J X : SSet.{u}} (t : K ⟶ J)
    {f g h i : J ⟶ X} {fq gq hq iq : K ⟶ X}
    (a : FunctorIso f g) (b : FunctorIso h g) (o : FunctorIso h i)
    (c : FunctorIso fq (t ≫ f)) (aq : FunctorIso fq gq) (bq : FunctorIso hq gq)
    (oq : FunctorIso hq iq) :
    (FunctorIso.precomp (a ≪≫ b.symm ≪≫ o) t).symm ≪≫ c.symm ≪≫ aq ≪≫ bq.symm ≪≫ oq =
    (o.precomp t).symm ≪≫ ((FunctorIso.precomp (a ≪≫ b.symm) t).symm ≪≫
      c.symm ≪≫ aq ≪≫ bq.symm) ≪≫ oq := by
  simp only [functorIso_precomp_trans, functorIso_precomp_symm, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc]

private lemma firstVertexNativeCoefficientIso_factorization {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] :
    firstVertexNativeCoefficientIso p = nativeUnderCoefficientIso p ≪≫
      (nativeBaseChangeCoefficientIso p).symm ≪≫
        nativeOppositeCoefficientIso (pullback.snd p (transportSimplexFirstVertexMap B)) := rfl

/-- 元の指定transport底変換は、同じpullbackの自然変換から来る反転区間辺の類。
HTT §3.3.2・Kerodon Tag 028Tの構成の特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "指定transportの底変換と元の反転区間辺の全図式での照合。"]
private lemma nativeTransportIntervalFactorization :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let t := U.map (nerveMap H)
  let ν₀ := (FunctorIso.precomp
      (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
    (simplexSectionBaseChangeCoefficient p k).symm ≪≫ nativeUnderCoefficientIso q ≪≫
      (nativeBaseChangeCoefficientIso q).symm
  ν = ((nativeOppositeCoefficientIso p₀).precomp t).symm ≪≫ ν₀ ≪≫
    nativeOppositeCoefficientIso r := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let t := U.map (nerveMap H)
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp t).symm ≪≫ diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let ν₀ := (FunctorIso.precomp
      (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
    (simplexSectionBaseChangeCoefficient p k).symm ≪≫ nativeUnderCoefficientIso q ≪≫
      (nativeBaseChangeCoefficientIso q).symm
  have h : ν = (FunctorIso.precomp
      ((leftClassificationSimplexIso p).symm ≪≫ θp) t).symm ≪≫
      (simplexSectionBaseChangeCoefficient p k).symm ≪≫
      (leftClassificationSimplexIso q).symm ≪≫ θq :=
    leftStraightening_baseChange_transport_normalized p k
  let Ψ := fun (s : FunctorIso (simplexSectionValue p) (leftCoherentTransport p₀))
      (s' : FunctorIso (simplexSectionValue q) (leftCoherentTransport r)) =>
      (s.precomp t).symm ≪≫ (simplexSectionBaseChangeCoefficient p k).symm ≪≫ s'
  have he := congrArg₂ Ψ (leftStraightening_firstVertexTransport_nativeCoefficients p)
    (leftStraightening_firstVertexTransport_nativeCoefficients q)
  have hd := congrArg₂ Ψ (firstVertexNativeCoefficientIso_factorization p)
    (firstVertexNativeCoefficientIso_factorization q)
  have ha := nativeTwistInverseChain t (nativeUnderCoefficientIso p)
    (nativeBaseChangeCoefficientIso p) (nativeOppositeCoefficientIso p₀)
    (simplexSectionBaseChangeCoefficient p k) (nativeUnderCoefficientIso q)
    (nativeBaseChangeCoefficientIso q) (nativeOppositeCoefficientIso r)
  have hmid := h.trans he
  have hmid' := hmid.trans hd
  exact hmid'.trans ha

private lemma nativeOppositeCoefficientIso_eq_universal {C : Type u} [Category.{u} C]
    {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p] :
    nativeOppositeCoefficientIso p =
      kanDiagramOppositeValueIso ⟨leftStrictTransportFunctor p, trivial⟩ :=
  kanEnrichedOppositeValueIso_eq_universal
    (relativeSectionEnrichedDiagram (strictTransportDomains C)) (leftFibrationObjectOf p)

private lemma nativeIntervalHom_core :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let Fh : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let hsrc : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change U.map (nerveMap H) ≫
      kanDiagramCoherentNerve (leftStrictTransportFunctor p₀ ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ leftStrictTransportFunctor p₀) ⋙ kanObjectOpFunctor)
    rw [kanDiagramCoherentNerve_precomp]
    rfl
  ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
    SSet.Truncated.HomotopyCategory.homMk ε.toTruncated := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let t := U.map (nerveMap H)
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let Fh : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) := ⟨leftStrictTransportFunctor r, trivial⟩
  let F₀ : KanDiagramObject (TransportSimplexCategory B) := ⟨leftStrictTransportFunctor p₀, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp t).symm ≪≫ diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let ν₀ := (FunctorIso.precomp
      (nativeUnderCoefficientIso p ≪≫ (nativeBaseChangeCoefficientIso p).symm) t).symm ≪≫
    (simplexSectionBaseChangeCoefficient p k).symm ≪≫ nativeUnderCoefficientIso q ≪≫
      (nativeBaseChangeCoefficientIso q).symm
  let hs₀ := kanDiagramCoherentNerve_precomp H F₀.val
  have hs : t ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change t ≫ kanDiagramCoherentNerve (F₀.val ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ F₀.val) ⋙ kanObjectOpFunctor)
    exact kanDiagramCoherentNerve_precomp H _
  have hop₀ : nativeOppositeCoefficientIso p₀ = kanDiagramOppositeValueIso F₀ :=
    nativeOppositeCoefficientIso_eq_universal p₀
  have hopr : nativeOppositeCoefficientIso r = kanDiagramOppositeValueIso Fr :=
    nativeOppositeCoefficientIso_eq_universal r
  have hopH : diagramIsoCongr hs₀ hs ((nativeOppositeCoefficientIso p₀).precomp t) =
      kanDiagramOppositeValueIso Fh := by
    rw [hop₀]
    exact kanDiagramOppositeValueIso_precomp H F₀
  have hν : ν = ((nativeOppositeCoefficientIso p₀).precomp t).symm ≪≫ ν₀ ≪≫
      nativeOppositeCoefficientIso r := nativeTransportIntervalFactorization p k
  have hn₀ : (diagramIsoCongr hs₀ rfl ν₀).hom = nativeRectangleHom Fh Fr α := by
    apply (normalizedIsoHom_iff hs₀ ν₀ (nativeRectangleHom Fh Fr α)).2
    exact leftStraighteningBaseChange_native_nonop_hom p k
  have hcast : diagramIsoCongr hs rfl ν = (kanDiagramOppositeValueIso Fh).symm ≪≫
      diagramIsoCongr hs₀ rfl ν₀ ≪≫ kanDiagramOppositeValueIso Fr := by
    rw [hν, diagramIsoCongr_trans_three hs hs₀ rfl rfl, diagramIsoCongr_symm hs₀ hs, hopH, hopr, normalizedIso_rfl (kanDiagramOppositeValueIso Fr)]
  let Fhop : KanDiagramObject (TransportSimplexCategory D) := ⟨Fh.val ⋙ kanObjectOpFunctor, trivial⟩
  let Frop : KanDiagramObject (TransportSimplexCategory D) := ⟨Fr.val ⋙ kanObjectOpFunctor, trivial⟩
  let αop : Fhop.val ⋙ kanObjectForget ⟶ Frop.val ⋙ kanObjectForget :=
    Functor.whiskerRight α SSet.opFunctor
  have hn : (diagramIsoCongr hs rfl ν).hom = nativeRectangleHom Fhop Frop αop := by
    rw [hcast]
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [hn₀]
    have he : nativeRectangleHom Fh Fr α ≫ (kanDiagramOppositeValueIso Fr).hom =
        (kanDiagramOppositeValueIso Fh).hom ≫ nativeRectangleHom Fhop Frop αop :=
      kanDiagramOppositeValueIso_naturality α
    rw [he]
    simp only [Iso.inv_hom_id_assoc]
  have hfinal : ν.hom = eqToHom
      (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hs) ≫ nativeRectangleHom Fhop Frop αop :=
    (normalizedIsoHom_iff hs ν (nativeRectangleHom Fhop Frop αop)).1 hn
  have he := kanDiagramOppositeHomInterval_natural_hom Fh Fr α
  change Truncated.HomotopyCategory.homMk
    (intervalMappingEdgeOfVertex ((kanDiagramOppositeHomInterval Fh Fr).app _
      (naturalHomVertex Fh Fr α))).toTruncated = nativeRectangleHom Fhop Frop αop at he
  change ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hs) ≫
    Truncated.HomotopyCategory.homMk
      (intervalMappingEdgeOfVertex ((kanDiagramOppositeHomInterval Fh Fr).app _
        (naturalHomVertex Fh Fr α))).toTruncated
  rw [he]
  exact hfinal

@[cite HTT "3.3.2" (partial := special) "指定transportの底変換と元の反転区間辺の全図式での照合。"]
private lemma leftStraighteningBaseChange_nativeInterval_hom :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let Fh : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) :=
    ⟨leftStrictTransportFunctor r, trivial⟩
  let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
    pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let hsrc : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
      kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) := by
    change U.map (nerveMap H) ≫
      kanDiagramCoherentNerve (leftStrictTransportFunctor p₀ ⋙ kanObjectOpFunctor) =
      kanDiagramCoherentNerve ((H ⋙ leftStrictTransportFunctor p₀) ⋙ kanObjectOpFunctor)
    rw [kanDiagramCoherentNerve_precomp]
    rfl
  ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hsrc) ≫
    SSet.Truncated.HomotopyCategory.homMk ε.toTruncated := by
  intro E B D hB hD p hp k
  exact nativeIntervalHom_core p k

open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

private lemma pointedProjection_of_under {A B : SSet.{u+1}}
    (F : B ⟶ SpaceInfinity.{u}) (g : A ⟶ leftUnstraightening F) (b : A ⟶ B)
    (hg : g ≫ leftUnstraighteningProjection F = b) :
    (g ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection = b ≫ F := by
  change (g ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection = b ≫ F
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun z => z ≫ F) hg

/-- 既存のscaffold制限と全写像空間の同じ族から、三つの指定pointed比較を記録する。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この模型での特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "scaffoldの指定三成分のpointed比較と射影の照合。"]
private lemma leftStraighteningBaseChange_scaffold_pointedEnds :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let Fh : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨H ⋙ leftStrictTransportFunctor p₀, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) :=
      ⟨leftStrictTransportFunctor r, trivial⟩
    let α : Fh.val ⋙ kanObjectForget ⟶ Fr.val ⋙ kanObjectForget :=
      pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
    let ε := intervalMappingEdgeOfVertex y
    let FH := kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor)
    let FR := kanDiagramCoherentNerve (Fr.val ⋙ kanObjectOpFunctor)
    let v := U.map (tautScaffold (Fh.val ⋙ kanObjectForget))
    let f₀ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫ pullback.fst pointedSpaceProjection FH
    let f₁ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫
      leftUnstraighteningEdgeLiftMap FH FR ε ≫ pullback.fst pointedSpaceProjection FR
    let fT := v ≫ U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val ≫
      pullback.fst pointedSpaceProjection FR
    ∃ (h₀ : (i ≫ R₀.pointedMap) ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
      (h₁ : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
      (hT : (i ≫ Rr.pointedMap) ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection),
      ∃ a₀ : FunctorIso (i ≫ R₀.pointedMap) f₀,
      ∃ a₁ : FunctorIso f₁ fT,
      ∃ aT : FunctorIso (i ≫ Rr.pointedMap) fT,
        a₀.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h₀) ∧
        a₁.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) h₁) ∧
        aT.postcomp pointedSpaceProjection = eqToIso
          (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT) := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let t := U.map (nerveMap H)
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
  let i := U.map s.val
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) t d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let F₀ : KanDiagramObject (TransportSimplexCategory B) := ⟨leftStrictTransportFunctor p₀, trivial⟩
  let Fh : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ F₀.val, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) := ⟨leftStrictTransportFunctor r, trivial⟩
  let L₀ := leftStrictTransportDiagram p₀
  let Lh := H ⋙ L₀
  let Lr := leftStrictTransportDiagram r
  let α : Lh ⟶ Lr := pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let FH := kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor)
  let FR := kanDiagramCoherentNerve (Fr.val ⋙ kanObjectOpFunctor)
  let v := U.map (tautScaffold Lh)
  let b := U.map (simplicialReplacementProjection Lh)
  let m := leftUnstraighteningEdgeLiftMap FH FR ε
  let c₀ := v ≫ oppositeKanUnstraighteningComparison Fh.val
  let c₁ := c₀ ≫ m
  let cT := v ≫ U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val
  let f₀ := c₀ ≫ pullback.fst pointedSpaceProjection FH
  let f₁ := c₁ ≫ pullback.fst pointedSpaceProjection FR
  let fT := cT ≫ pullback.fst pointedSpaceProjection FR
  have hb : i ≫ U.map r = b := by
    simpa only [i, b, Functor.map_comp] using congrArg U.map s.property.2.1
  have hs : t ≫ leftCoherentTransport p₀ = FH := by
    exact kanDiagramCoherentNerve_precomp H (F₀.val ⋙ kanObjectOpFunctor)
  have hc₀ : c₀ ≫ leftUnstraighteningProjection FH = b := by
    dsimp only [c₀]
    rw [Category.assoc, oppositeKanUnstraighteningComparison_projection]
    dsimp only [v, b]
    change U.map (tautScaffold Lh) ≫ U.map (weightedNerveProjection Lh) =
      U.map (simplicialReplacementProjection Lh)
    rw [← U.map_comp, tautScaffold_projection]
  have hc₁ : c₁ ≫ leftUnstraighteningProjection FR = b := by
    change (c₀ ≫ m) ≫ leftUnstraighteningProjection FR = b
    rw [Category.assoc, leftUnstraighteningEdgeLiftMap_projection]
    exact hc₀
  have hcT : cT ≫ leftUnstraighteningProjection FR = b := by
    dsimp only [cT]
    rw [Category.assoc, Category.assoc, oppositeKanUnstraighteningComparison_projection]
    change U.map (tautScaffold Lh) ≫
      U.map (weightedNerveMap α) ≫ U.map (weightedNerveProjection Lr) = b
    rw [← U.map_comp, weightedNerveMap_projection, ← U.map_comp, tautScaffold_projection]
  have hf₀ : f₀ ≫ pointedSpaceProjection = b ≫ FH := pointedProjection_of_under FH c₀ b hc₀
  have hf₁ : f₁ ≫ pointedSpaceProjection = b ≫ FR := pointedProjection_of_under FR c₁ b hc₁
  have hfT : fT ≫ pointedSpaceProjection = b ≫ FR := pointedProjection_of_under FR cT b hcT
  have hRD : R₀.diagram = t ≫ leftCoherentTransport p₀ :=
    (nerveLeftTransportRepresentation p₀).cartesianRestrict_diagram _ _ _
  have hRP : R₀.pointedMap = U.map d.val ≫ (nerveLeftTransportRepresentation p₀).pointedMap :=
    (nerveLeftTransportRepresentation p₀).cartesianRestrict_pointedMap _ _ _
  have hA : (i ≫ R₀.pointedMap) ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection := by
    calc
      _ = (i ≫ U.map r) ≫ R₀.diagram := by
        rw [Category.assoc, R₀.pointedMap_projection, ← Category.assoc]
      _ = b ≫ (t ≫ leftCoherentTransport p₀) := congrArg₂ (fun a b => a ≫ b) hb hRD
      _ = b ≫ FH := congrArg (fun F => b ≫ F) hs
      _ = _ := hf₀.symm
  have hB : (i ≫ Rr.pointedMap) ≫ pointedSpaceProjection = b ≫ FR := by
    rw [Category.assoc, Rr.pointedMap_projection, ← Category.assoc, hb]
    rfl
  let hN := hf₁.trans hfT.symm
  let hT := hB.trans hfT.symm
  obtain ⟨hfP, hgP, ⟨eP⟩⟩ := scaffoldPointedRelativeIso p₀
  let fP := U.map (universalScaffold p₀) ≫ (nerveLeftTransportRepresentation p₀).pointedMap
  let gP := U.map (tautScaffold L₀) ≫ leftCoherentTransportComparison p₀ ≫
    pullback.fst pointedSpaceProjection (leftCoherentTransport p₀)
  let jP := U.map (simplicialReplacementBaseMap H L₀)
  have hiP : i ≫ U.map d.val = jP ≫ U.map (universalScaffold p₀) := by
    simpa only [i, jP, Functor.map_comp] using congrArg U.map s.property.1
  have hsourceP : jP ≫ fP = i ≫ R₀.pointedMap := by
    rw [hRP]
    dsimp only [fP]
    rw [← Category.assoc, ← hiP, Category.assoc]
  have htP : jP ≫ U.map (tautScaffold L₀) = v ≫ U.map (weightedNerveBaseMap H L₀) := by
    simpa only [jP, v, Functor.map_comp] using
      (congrArg U.map (tautScaffold_baseMap H L₀)).symm
  have htargetP : jP ≫ gP = f₀ := by
    calc
      _ = (jP ≫ U.map (tautScaffold L₀)) ≫
          (oppositeKanUnstraighteningComparison F₀.val ≫
            pullback.fst pointedSpaceProjection (leftCoherentTransport p₀)) :=
        (Category.assoc _ _ _).symm
      _ = (v ≫ U.map (weightedNerveBaseMap H L₀)) ≫
          (oppositeKanUnstraighteningComparison F₀.val ≫
            pullback.fst pointedSpaceProjection (leftCoherentTransport p₀)) :=
        congrArg (fun a => a ≫ (oppositeKanUnstraighteningComparison F₀.val ≫
          pullback.fst pointedSpaceProjection (leftCoherentTransport p₀))) htP
      _ = v ≫ (oppositeKanUnstraighteningComparison Fh.val ≫ pullback.fst pointedSpaceProjection FH) := by
        exact (Category.assoc _ _ _).trans
          (congrArg (fun z => v ≫ z) (oppositeComparisonPointedBase H F₀.val).symm)
      _ = f₀ := (Category.assoc _ _ _).symm
  let aA := functorIsoOfEq ((relativeFunctorVertexIsoImage pointedSpaceProjection
      (U.map (simplicialReplacementProjection L₀) ≫ leftCoherentTransport p₀)
      fP gP hfP hgP eP).precomp jP) hsourceP htargetP
  have haA : aA.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hA) :=
    relativeFunctorVertexIsoImage_transport_projection _ _ fP gP hfP hgP eP jP hsourceP htargetP hA
  obtain ⟨hfR, hgR, ⟨eR⟩⟩ := scaffoldPointedRelativeIso r
  let fR := U.map (universalScaffold r) ≫ Rr.pointedMap
  let gR := U.map (tautScaffold Lr) ≫ leftCoherentTransportComparison r ≫ pullback.fst pointedSpaceProjection FR
  let jR := U.map (simplicialReplacementMap α)
  have hiR : i = jR ≫ U.map (universalScaffold r) := by
    simpa only [i, jR, Functor.map_comp] using
      congrArg U.map (scaffoldPullbackData_eq p₀ r d.val H d.property.2.2.1)
  have hsourceR : jR ≫ fR = i ≫ Rr.pointedMap := by
    dsimp only [fR]
    rw [← Category.assoc, ← hiR]
  have htR : jR ≫ U.map (tautScaffold Lr) = v ≫ U.map (weightedNerveMap α) := by
    simpa only [jR, v, Functor.map_comp] using congrArg U.map (tautScaffold_map α)
  have htargetR : jR ≫ gR = fT := by
    dsimp only [gR, fT, cT]
    rw [← Category.assoc jR, htR]
    simp only [Category.assoc]
    rfl
  let aT := functorIsoOfEq ((relativeFunctorVertexIsoImage pointedSpaceProjection
      (U.map (simplicialReplacementProjection Lr) ≫ FR) fR gR hfR hgR eR).precomp jR)
    hsourceR htargetR
  have haT : aT.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT) :=
    relativeFunctorVertexIsoImage_transport_projection _ _ fR gR hfR hgR eR jR hsourceR htargetR hT
  let my := CartesianMonoidalCategory.lift (𝟙 (leftUnstraightening FH)) (SSet.const y) ≫
    leftUnstraighteningMappingFamily FH FR
  let nSrc := oppositeKanUnstraighteningComparison Fh.val ≫ my
  let nTgt := U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val
  obtain ⟨hgN, hfN, ⟨eN⟩⟩ := oppositeHomComparison_at_natural Fh Fr α
  obtain ⟨hfNB, hgNB, ⟨eNB⟩⟩ := relativeFunctorBaseChangeForward_vertexIso
    pointedSpaceProjection FR (U.map (weightedNerveProjection Lh)) nSrc nTgt hgN hfN eN
  have hy : intervalMappingVertexOfEdge ε = y :=
    (intervalMappingEdgeVertexEquiv (functorVertex FH) (functorVertex FR)).apply_symm_apply y
  have hm : my = m := by
    exact (congrArg (fun z => CartesianMonoidalCategory.lift (𝟙 (leftUnstraightening FH))
      (SSet.const z) ≫ leftUnstraighteningMappingFamily FH FR) hy).symm
  have hsourceN : v ≫ (nSrc ≫ pullback.fst pointedSpaceProjection FR) = f₁ := by
    dsimp only [nSrc, f₁, c₁, c₀]
    simp only [Category.assoc]
    exact congrArg (fun z => v ≫ oppositeKanUnstraighteningComparison Fh.val ≫ z ≫
      pullback.fst pointedSpaceProjection FR) hm
  have htargetN : v ≫ (nTgt ≫ pullback.fst pointedSpaceProjection FR) = fT := by
    dsimp only [nTgt, fT, cT]
    simp only [Category.assoc]
  let aN := functorIsoOfEq ((relativeFunctorVertexIsoImage pointedSpaceProjection
      (U.map (weightedNerveProjection Lh) ≫ FR)
      (nSrc ≫ pullback.fst pointedSpaceProjection FR) (nTgt ≫ pullback.fst pointedSpaceProjection FR)
      hfNB hgNB eNB).precomp v) hsourceN htargetN
  have haN : aN.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hN) :=
    relativeFunctorVertexIsoImage_transport_projection _ _ _ _ hfNB hgNB eNB v hsourceN htargetN hN
  exact ⟨hA, hN, hT, aA, aN, aT, haA, haN, haT⟩

/-- 指定した同じ辺の持ち上げの射影を、指定同型の前合成で記録する。 -/
private lemma edgeLift_pointedIso {A B : SSet.{u+1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u})
      (functorVertex F) (functorVertex G))
    (d : FunctorIso F G)
    (hd : d.hom = SSet.Truncated.HomotopyCategory.homMk e.toTruncated)
    (c : A ⟶ leftUnstraightening F) (b : A ⟶ B)
    (hc : c ≫ leftUnstraighteningProjection F = b)
    (f g : A ⟶ PointedSpaceInfinity.{u})
    (hf : f = c ≫ pullback.fst pointedSpaceProjection F)
    (hg : g = c ≫ leftUnstraighteningEdgeLiftMap F G e ≫
      pullback.fst pointedSpaceProjection G)
    (hfp : f ≫ pointedSpaceProjection = b ≫ F)
    (hgp : g ≫ pointedSpaceProjection = b ≫ G) :
    ∃ a : FunctorIso f g, a.postcomp pointedSpaceProjection =
      functorIsoOfEq (d.precomp b) hfp.symm hgp.symm := by
  let r := e.map ((pre b).app SpaceInfinity.{u})
  have hr : (d.precomp b).hom = SSet.Truncated.HomotopyCategory.homMk r.toTruncated := by
    rw [functorIso_precomp_hom, hd]
    rfl
  let r' := r.ofEq (congrArg functorVertex hfp.symm) (congrArg functorVertex hgp.symm)
  let W := (Δ[1] ◁ c) ≫ leftUnstraighteningEdgeLiftFamily F G e
  have h₀ : prismEndpoint 0 A ≫ W = f := by
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      leftUnstraighteningEdgeLiftFamily_zero]
    exact hf.symm
  have h₁ : prismEndpoint 1 A ≫ W = g := by
    dsimp only [W]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      leftUnstraighteningEdgeLiftFamily_one]
    exact hg.symm
  have hp : W ≫ pointedSpaceProjection = functorEdgePrism r'.toTruncated := by
    dsimp only [W]
    rw [Category.assoc, leftUnstraighteningEdgeLiftFamily_projection, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, hc]
    exact (functorEdgePrism_precomp e.toTruncated b).symm
  exact pointedIsoOfProjectedPrism _ r'.toTruncated
    (functorIsoOfEq_hom (d.precomp b) hfp.symm hgp.symm r hr).symm W h₀ h₁ hp

/-- 指定同型の両端に入る等式の同型は、同じ端点移送に吸収される。 -/
private lemma pointedProjection_chain {A X : SSet.{u}}
    {fA f₀ f₁ fT fB l r : A ⟶ X}
    (hA : fA = f₀) (hN : f₁ = fT) (hT : fB = fT)
    (h₀ : l = f₀) (h₁ : r = f₁) (hF : l = fA) (hG : r = fB)
    (e : FunctorIso l r) :
    eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hA) ≪≫
      diagramIsoCongr h₀ h₁ e ≪≫
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hN) ≪≫
      (eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT)).symm =
        diagramIsoCongr hF hG e := by
  subst f₀ fT fB l r
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 同じ前合成射の等式は、指定同型の前合成の異種等式を与える。 -/
private lemma functorIsoPrecomp_heq {A D X : SSet.{u}}
    {f g : A ⟶ X} (e : FunctorIso f g) {i j : D ⟶ A} (h : i = j) :
    HEq (e.precomp i) (e.precomp j) := by
  cases h
  rfl

/-- 四つの既存比較の射影は、元の指定同型を同じ外端点へ移したものである。 -/
private lemma pointedProjection_fourChain {A : SSet.{u+1}}
    {fA f₀ f₁ fT fB : A ⟶ PointedSpaceInfinity.{u}}
    {l r : A ⟶ SpaceInfinity.{u}}
    (aA : FunctorIso fA f₀) (aM : FunctorIso f₀ f₁)
    (aN : FunctorIso f₁ fT) (aT : FunctorIso fB fT)
    (hA : fA ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
    (hN : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
    (hT : fB ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
    (h₀ : l = f₀ ≫ pointedSpaceProjection) (h₁ : r = f₁ ≫ pointedSpaceProjection)
    (hF : l = fA ≫ pointedSpaceProjection) (hG : r = fB ≫ pointedSpaceProjection)
    (e : FunctorIso l r)
    (haA : aA.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hA))
    (haM : aM.postcomp pointedSpaceProjection = diagramIsoCongr h₀ h₁ e)
    (haN : aN.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hN))
    (haT : aT.postcomp pointedSpaceProjection =
      eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hT)) :
    FunctorIso.postcomp (aA ≪≫ aM ≪≫ aN ≪≫ aT.symm) pointedSpaceProjection =
      diagramIsoCongr hF hG e := by
  rw [functorIso_postcomp_trans, functorIso_postcomp_trans, functorIso_postcomp_trans,
    functorIso_postcomp_symm, haA, haM, haN, haT]
  exact pointedProjection_chain hA hN hT h₀ h₁ hF hG e

/-- 同じ二段の前合成と端点移送を、一度の前合成へまとめる。 -/
private lemma normalizedIso_precomp_pair {A B Z X : SSet.{u}}
    {F G : B ⟶ X} (e : FunctorIso F G)
    (p : A ⟶ B) (i : Z ⟶ A) (b : Z ⟶ B) (hb : i ≫ p = b)
    (f g : A ⟶ X) (hf : f = p ≫ F) (hg : g = p ≫ G)
    (hF : b ≫ F = i ≫ f) (hG : b ≫ G = i ≫ g) :
    diagramIsoCongr hF hG (e.precomp b) =
      (functorIsoOfEq (e.precomp p) hf.symm hg.symm).precomp i := by
  rw [functorIsoOfEq_eq_diagramIsoCongr, diagramIsoCongr_precomp]
  have he : HEq ((e.precomp p).precomp i) (e.precomp b) := by
    rw [functorIso_precomp_precomp]
    exact functorIsoPrecomp_heq e hb
  exact diagramIsoCongr_eq_of_heq hF hG _ _ _ _ he.symm

/-- 両端と中間の指定pointed比較を、同じ図式同型の制限へ接続する法則。 -/
private lemma pointedComparisonOfEnds {A B Z : SSet.{u+1}}
    (p : A ⟶ B) (i : Z ⟶ A) (b : Z ⟶ B) (hb : i ≫ p = b)
    (F F' G : B ⟶ SpaceInfinity.{u}) (hs : F = F') (ν : FunctorIso F G)
    (ε : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u}) (functorVertex F') (functorVertex G))
    (hε : (diagramIsoCongr hs rfl ν).hom = Truncated.HomotopyCategory.homMk ε.toTruncated)
    (f g : A ⟶ PointedSpaceInfinity.{u})
    (hf : f ≫ pointedSpaceProjection = p ≫ F) (hg : g ≫ pointedSpaceProjection = p ≫ G)
    (c : Z ⟶ leftUnstraightening F') (hc : c ≫ leftUnstraighteningProjection F' = b)
    (f₀ f₁ fT : Z ⟶ PointedSpaceInfinity.{u})
    (h₀ : f₀ = c ≫ pullback.fst pointedSpaceProjection F')
    (h₁ : f₁ = c ≫ leftUnstraighteningEdgeLiftMap F' G ε ≫ pullback.fst pointedSpaceProjection G)
    (geometry : ∃ (hA : (i ≫ f) ≫ pointedSpaceProjection = f₀ ≫ pointedSpaceProjection)
      (hN : f₁ ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection)
      (hT : (i ≫ g) ≫ pointedSpaceProjection = fT ≫ pointedSpaceProjection),
      ∃ aA : FunctorIso (i ≫ f) f₀, ∃ aN : FunctorIso f₁ fT, ∃ aT : FunctorIso (i ≫ g) fT,
        aA.postcomp pointedSpaceProjection =
            eqToIso (congrArg (fun z => HomotopyCategory.mk (functorVertex z)) hA) ∧
        aN.postcomp pointedSpaceProjection =
            eqToIso (congrArg (fun z => HomotopyCategory.mk (functorVertex z)) hN) ∧
        aT.postcomp pointedSpaceProjection =
            eqToIso (congrArg (fun z => HomotopyCategory.mk (functorVertex z)) hT)) :
    ∃ e : FunctorIso (i ≫ f) (i ≫ g), e.postcomp pointedSpaceProjection =
      (functorIsoOfEq (ν.precomp p) hf.symm hg.symm).precomp i := by
  obtain ⟨hA, hN, hT, aA, aN, aT, haA, haN, haT⟩ := geometry
  have hc₁ : (c ≫ leftUnstraighteningEdgeLiftMap F' G ε) ≫
      leftUnstraighteningProjection G = b := by
    rw [Category.assoc, leftUnstraighteningEdgeLiftMap_projection]
    exact hc
  have hf₀ : f₀ ≫ pointedSpaceProjection = b ≫ F' := by
    rw [h₀]
    exact pointedProjection_of_under F' c b hc
  have hf₁ : f₁ ≫ pointedSpaceProjection = b ≫ G := by
    rw [h₁]
    exact pointedProjection_of_under G (c ≫ leftUnstraighteningEdgeLiftMap F' G ε) b hc₁
  let δ := diagramIsoCongr hs rfl ν
  obtain ⟨aM, haM⟩ := edgeLift_pointedIso F' G ε δ hε c b hc f₀ f₁ h₀ h₁ hf₀ hf₁
  have hF : b ≫ F = (i ≫ f) ≫ pointedSpaceProjection :=
    (congrArg (fun z => b ≫ z) hs).trans (hf₀.symm.trans hA.symm)
  have hG : b ≫ G = (i ≫ g) ≫ pointedSpaceProjection := by
    exact (congrArg (fun z => z ≫ G) hb).symm.trans (congrArg (fun z => i ≫ z) hg.symm)
  let h₀' := (congrArg (fun z => b ≫ z) hs).trans hf₀.symm
  let h₁' := hf₁.symm
  have hmid : functorIsoOfEq (δ.precomp b) hf₀.symm hf₁.symm =
      diagramIsoCongr h₀' h₁' (ν.precomp b) := by
    rw [functorIsoOfEq_eq_diagramIsoCongr, diagramIsoCongr_precomp, diagramIsoCongr_comp]
  refine ⟨aA ≪≫ aM ≪≫ aN ≪≫ aT.symm, ?_⟩
  exact (pointedProjection_fourChain aA aM aN aT hA hN hT h₀' h₁' hF hG
    (ν.precomp b) haA (haM.trans hmid) haN haT).trans
      (normalizedIso_precomp_pair ν p i b hb (f ≫ pointedSpaceProjection)
        (g ≫ pointedSpaceProjection) hf hg hF hG)

/-- 同じ区間の辺を表す任意の指定同型に対する、scaffold上の接続の法則。 -/
private lemma scaffoldPointedComparison_of_intervalHom :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let F₀ : KanDiagramObject (TransportSimplexCategory B) := ⟨leftStrictTransportFunctor p₀, trivial⟩
    let Fh : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ F₀.val, trivial⟩
    let Fr : KanDiagramObject (TransportSimplexCategory D) := ⟨leftStrictTransportFunctor r, trivial⟩
    let α := pullbackStrictComparison p₀ r d.val H d.property.2.2.1
    let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
    let ε := intervalMappingEdgeOfVertex y
    let hs : U.map (nerveMap H) ≫ leftCoherentTransport p₀ =
        kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor) :=
      kanDiagramCoherentNerve_precomp H (F₀.val ⋙ kanObjectOpFunctor)
    ∀ (ν : FunctorIso (U.map (nerveMap H) ≫ leftCoherentTransport p₀) (leftCoherentTransport r)),
      ν.hom = eqToHom (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) hs) ≫
        SSet.Truncated.HomotopyCategory.homMk ε.toTruncated →
    ∃ e : FunctorIso (i ≫ R₀.pointedMap) (i ≫ Rr.pointedMap),
      e.postcomp pointedSpaceProjection =
        (functorIsoOfEq (FunctorIso.precomp ν (U.map r)) R₀.pointedMap_projection.symm
          Rr.pointedMap_projection.symm).precomp i := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let t := U.map (nerveMap H)
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
  let i := U.map s.val
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) t d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let F₀ : KanDiagramObject (TransportSimplexCategory B) := ⟨leftStrictTransportFunctor p₀, trivial⟩
  let Fh : KanDiagramObject (TransportSimplexCategory D) := ⟨H ⋙ F₀.val, trivial⟩
  let Fr : KanDiagramObject (TransportSimplexCategory D) := ⟨leftStrictTransportFunctor r, trivial⟩
  let L₀ := leftStrictTransportDiagram p₀
  let Lh := H ⋙ L₀
  let Lr := leftStrictTransportDiagram r
  let α : Lh ⟶ Lr := pullbackStrictComparison p₀ r d.val H d.property.2.2.1
  let y := (kanDiagramOppositeHomInterval Fh Fr).app _ (naturalHomVertex Fh Fr α)
  let ε := intervalMappingEdgeOfVertex y
  let FH := kanDiagramCoherentNerve (Fh.val ⋙ kanObjectOpFunctor)
  let FR := kanDiagramCoherentNerve (Fr.val ⋙ kanObjectOpFunctor)
  let v := U.map (tautScaffold Lh)
  let b := U.map (simplicialReplacementProjection Lh)
  let m := leftUnstraighteningEdgeLiftMap FH FR ε
  let c₀ := v ≫ oppositeKanUnstraighteningComparison Fh.val
  let c₁ := c₀ ≫ m
  let cT := v ≫ U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val
  let f₀ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫
    pullback.fst pointedSpaceProjection FH
  let f₁ := v ≫ oppositeKanUnstraighteningComparison Fh.val ≫ m ≫
    pullback.fst pointedSpaceProjection FR
  let fT := v ≫ U.map (weightedNerveMap α) ≫ oppositeKanUnstraighteningComparison Fr.val ≫
    pullback.fst pointedSpaceProjection FR
  dsimp only
  intro ν hν
  have hb : i ≫ U.map r = b := by
    simpa only [i, b, Functor.map_comp] using congrArg U.map s.property.2.1
  have hs : t ≫ leftCoherentTransport p₀ = FH :=
    kanDiagramCoherentNerve_precomp H (F₀.val ⋙ kanObjectOpFunctor)
  have hc₀ : c₀ ≫ leftUnstraighteningProjection FH = b := by
    dsimp only [c₀]
    rw [Category.assoc, oppositeKanUnstraighteningComparison_projection]
    change U.map (tautScaffold Lh) ≫ U.map (weightedNerveProjection Lh) =
      U.map (simplicialReplacementProjection Lh)
    rw [← U.map_comp, tautScaffold_projection]
  exact pointedComparisonOfEnds (U.map r) i b hb
    (t ≫ leftCoherentTransport p₀) FH FR hs ν ε
    ((normalizedIsoHom_iff hs ν _).2 hν) R₀.pointedMap Rr.pointedMap
    R₀.pointedMap_projection Rr.pointedMap_projection c₀ hc₀ f₀ f₁ fT
    (Category.assoc v (oppositeKanUnstraighteningComparison Fh.val) _).symm
    (Category.assoc v (oppositeKanUnstraighteningComparison Fh.val) _).symm
    (leftStraighteningBaseChange_scaffold_pointedEnds p k)


/-- scaffoldの指定pointed比較は、元の同じνの制限を被覆する。
HTT §3.3.2・Kerodon Tag 028Tの構成に付随する、この模型での特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "scaffold制限上の指定pointed比較と分類底変換の射影の照合。"]
private lemma leftStraighteningBaseChange_scaffold_pointedComparison :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
    let U := SSet.uliftFunctor.{u+1,u}
    let lB := transportSimplexFirstVertexMap B
    let lD := transportSimplexFirstVertexMap D
    let H := transportSimplexFunctor k
    let q := pullback.snd p k
    let p₀ := pullback.snd p lB
    let r := pullback.snd q lD
    let d := leftStraighteningBaseChangePullbackData p k
    let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
    let i := U.map s.val
    let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
      (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
    let Rr := nerveLeftTransportRepresentation r
    let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
    let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
    let β := leftStraighteningInfinityDiagram_baseChangeIso p k
    let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
      diagramIsoCongr
        (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
          Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
    ∃ e : FunctorIso (i ≫ R₀.pointedMap) (i ≫ Rr.pointedMap),
      e.postcomp pointedSpaceProjection =
        (functorIsoOfEq (FunctorIso.precomp ν (U.map r)) R₀.pointedMap_projection.symm
          Rr.pointedMap_projection.symm).precomp i := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
  let i := U.map s.val
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν : FunctorIso (U.map (nerveMap H) ≫ leftCoherentTransport p₀)
      (leftCoherentTransport r) := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  exact scaffoldPointedComparison_of_intervalHom p k ν
    (leftStraighteningBaseChange_nativeInterval_hom p k)

/-- 底変換の元の指定νの辺を被覆し、元の二つのpointed比較を結ぶprism。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この指定scaffold模型での特殊な照合。 -/
@[cite HTT "3.3.2" (partial := special) "指定底変換同型の辺を被覆するpointed比較のprism。"]
public lemma leftStraighteningBaseChange_pointedPrism :
    ∀ {E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
  (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B),
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let e := functorEdgeOfSimplicialHomotopy (functorHomHomotopy ν.hom)
  ∃ W : (Δ[1] : SSet.{u+1}) ⊗ U.obj (pullback q lD) ⟶ PointedSpaceInfinity.{u},
    prismEndpoint 0 (U.obj (pullback q lD)) ≫ W = R₀.pointedMap ∧
    prismEndpoint 1 (U.obj (pullback q lD)) ≫ W = Rr.pointedMap ∧
    W ≫ pointedSpaceProjection = (Δ[1] ◁ U.map r) ≫ functorEdgePrism e := by
  intro E B D hB hD p hp k
  let U := SSet.uliftFunctor.{u+1,u}
  let lB := transportSimplexFirstVertexMap B
  let lD := transportSimplexFirstVertexMap D
  let H := transportSimplexFunctor k
  let q := pullback.snd p k
  let p₀ := pullback.snd p lB
  let r := pullback.snd q lD
  let d := leftStraighteningBaseChangePullbackData p k
  let R₀ := (nerveLeftTransportRepresentation p₀).cartesianRestrict
    (U.map d.val) (U.map (nerveMap H)) d.property.2.2.2
  let Rr := nerveLeftTransportRepresentation r
  let θp := leftStraighteningInfinityDiagram_firstVertexTransportIso p
  let θq := leftStraighteningInfinityDiagram_firstVertexTransportIso q
  let β := leftStraighteningInfinityDiagram_baseChangeIso p k
  let ν : FunctorIso (U.map (nerveMap H) ≫ leftCoherentTransport p₀)
      (leftCoherentTransport r) := (θp.precomp (U.map (nerveMap H))).symm ≪≫
    diagramIsoCongr
      (by rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k,
        Category.assoc]) rfl (β.precomp (U.map lD)) ≪≫ θq
  let s := scaffoldPullbackData p₀ r d.val H d.property.2.2.1
  let i := U.map s.val
  obtain ⟨e, he⟩ := leftStraighteningBaseChange_scaffold_pointedComparison p k
  exact pointedPrismOfRestriction (U.map r) i (uliftPrecomp s.val s.property.2.2) ν
    R₀.pointedMap_projection Rr.pointedMap_projection e he

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
