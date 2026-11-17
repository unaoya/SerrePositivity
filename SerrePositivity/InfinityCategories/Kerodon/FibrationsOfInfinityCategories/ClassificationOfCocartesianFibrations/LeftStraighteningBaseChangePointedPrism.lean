module

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

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
