module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanWeightedUnstraighteningUnit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PinchedObjectNaturality

/-!
概要：集合値重みの制限射と、指定した weighted 比較による G8 の写像空間同値（正本）。
C3：新しい利用者は Natural 版を使う。旧比較は互換用の deprecated 宣言として保持する。
方針：要素の圏の比較に実射を用い、極限への制限は錐の普遍性から作る。
規約：指定極限錐を受け取る。G8 の自然性全体の四角形は、このファイルでは未証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors
open MonoidalClosed
namespace SetWeight

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}

/-- 定値単体的集合の反転は、同じ集合値係数に自然同型。 -/
def coefficientsOppositeIso (P : I ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients P ≅ (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros; rfl)) (by intros; rfl)

def coefficientsOppositeWeightedIso (P : I ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients P) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve ((P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (Over.forget (nerve I)).mapIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFunctor I).mapIso (coefficientsOppositeIso P))

/-- 元のラベルを、反転係数の指定された coslice 比較へ写す。
底上の同値の無指定な選択を介さず、weighted 比較の実射を使う。 -/
def elementsComparisonNatural (P : I ⥤ Type u) :
    nerve P.Elements ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram P) :=
  _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients P) ≫
    (coefficientsOppositeWeightedIso P).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallReversedWeightedKanUnstraighteningComparison (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan)

lemma elementsComparisonNatural_projection (P : I ⥤ Type u) :
    elementsComparisonNatural P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram P) =
      _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.projection P := by
  simp only [elementsComparisonNatural, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallReversedWeightedKanUnstraighteningComparison_projection]
  have h : (coefficientsOppositeWeightedIso P).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection ((P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients P) :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFunctor I).mapIso (coefficientsOppositeIso P)).hom.w
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection, _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement_projection]

lemma elementsComparisonNatural_isPrecompositionEquivalence (P : I ⥤ Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (elementsComparisonNatural P) := by
  let : ∀ i, KanComplex
      (((P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj i) :=
    fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan.obj (P.obj i))).isKanComplex
  have hb := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningLift_isPrecompositionEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection ((P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reversedWeightedKanUnstraighteningComparison (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reversedWeightedKanUnstraighteningComparison_projection (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reversedWeightedKanUnstraighteningComparison_isPrecompositionEquivalence (P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement P))).comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients P)).comp
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (coefficientsOppositeWeightedIso P)).comp hb))

/-- P を始域とする変換の空間を、P.Elements 上の同じ図式の切断空間に移す。 -/
def sectionsEquivalenceNatural (P : I ⥤ Type u)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
      ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSpaceSectionsObject (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram P G)).obj) := by
  let X := _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram P
  let p := _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.projection P
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection G
  let q' := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram P G)
  have : ∀ n, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).obj n) :=
    fun n => inferInstanceAs (Small.{u} (ULift.{u + 1} ((nerve I).obj n)))
  let e₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.small_leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence X G).choose
  let e₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningRelativeFunctorIso X G).symm
  let j : Over.mk p ⟶ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection X) :=
    Over.homMk (elementsComparisonNatural P) (elementsComparisonNatural_projection P)
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeFunctorOverPre_isQCatEquivalence q j
    (elementsComparisonNatural_isPrecompositionEquivalence P)
  let bp : Over.mk q' ≅ Over.mk (pullback.snd q p) :=
    Over.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningBaseChangeIso G p)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningBaseChangeIso_hom_snd G p)
  let e₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections q' :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.pullbackSectionsRelativeIso q p).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso _ ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverIso (Iso.refl (Over.mk (𝟙 _))) bp.symm ≪≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialSectionsRelativeIso q').symm
  exact e₀.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e₁).trans
    (hj.ulift.choose.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso e₂))))

/-- 集合値前層 P で重み付けたテンソルからの写像空間。
右辺には、呼び出し側が指定した元の圏上の極限錐そのものを使う。 -/
def tensorSpaceFunctor_setWeightHomNatural (P : I ⥤ Type u)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram P F)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor hE M)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom M c.vertex) := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.spaceTensorData hE M
  let g := _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram P (F ≫ t.hom)
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone t.hom c) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction t.adjunction c hc
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone g) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone t.hom c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_isLimit g) hg
  have ev : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSpaceSectionsVertex g) (t.hom.app _ c.vertex) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentDiagramSectionsCone_vertex g]
    exact e
  letI : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection g)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSpaceSectionsObject g).isKanComplex
  let vs := _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.spaceValueEquivalence ev
  let hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentSpaceSectionsVertex_object g))).symm.trans vs
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor_diagramHom hE M (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram P) F).trans
    ((sectionsEquivalenceNatural P (F ≫ t.hom)).trans (hs.isQCatEquivalence.ulift.choose.trans
      ((_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.spaceUniverseValueEquivalence (t.hom.app _ c.vertex)).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.spaceValueEquivalence (t.represents.app (ULift.up c.vertex))).symm.trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.covariantRepresentableValueEquivalence M c.vertex)))))


/-- 集合値の射を離散 Kan 値係数の射として使う。 -/
def coefficientsMap (φ : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients X ⟶ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients Y :=
  Functor.whiskerRight (Functor.whiskerRight φ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan) _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget

/-- 元の圏と simplicial replacement のラベル比較は重みの射に自然。 -/
lemma elementsToReplacement_naturality (φ : X ⟶ Y) :
    nerveMap φ.mapElements ≫ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement Y =
      _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementMap (coefficientsMap φ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- weighted nerve へのラベル比較も同じ係数射に自然。 -/
lemma elementsWeighted_naturality (φ : X ⟶ Y) :
    nerveMap φ.mapElements ≫ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients Y) =
      (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.elementsToReplacement X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.coefficients X)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (coefficientsMap φ) := by
  rw [← Category.assoc, elementsToReplacement_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_map, ← Category.assoc]

/-- 重みの射を coherent な空間値図式間の辺へ写す。 -/
def spaceDiagramEdge (φ : X ⟶ Y) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram Y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramNaturalTransformationEdge
    (F := ⟨X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan, trivial⟩) (G := ⟨Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.setsToKan, trivial⟩) (coefficientsMap φ)

/-- 重みの射にテンソルを後合成した、前層の圏の辺。 -/
def tensorWeightEdge {E : SSet.{u + 1}} [Quasicategory E]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (M : E _⦋0⦌) (φ : X ⟶ Y) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor hE M))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor hE M)) :=
  (spaceDiagramEdge φ).map
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor hE M))

/-- G8 の随伴比較は、重みの射による前合成に自然。 -/
def tensorSpaceFunctor_diagramHom_weight_naturality
    {E : SSet.{u + 1}} [Quasicategory E] (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (M : E _⦋0⦌) (φ : X ⟶ Y)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)
        (Truncated.HomotopyCategory.homMk (tensorWeightEdge hE M φ).toTruncated) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor_diagramHom hE M (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram X) F).hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor_diagramHom hE M (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram Y) F).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.spaceTensorData hE M).hom))
          (Truncated.HomotopyCategory.homMk (spaceDiagramEdge φ).toTruncated)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.spaceTensorData hE M).adjunction
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).pinchedMapNaturalityLeftIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (Truncated.HomotopyCategory.homMk (spaceDiagramEdge φ).toTruncated)

/-- 重みの射が元の圏の脈体に誘導する射。 -/
def elementsMap (φ : X ⟶ Y) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements)

variable {E : SSet.{u + 1}}
  (φ : X ⟶ Y) (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)

/-- 元の圏の関手は、係数図式への射影を保つ。 -/
lemma elementsMap_diagram : elementsMap φ ≫ _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F = _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F := by
  dsimp [elementsMap, _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram, _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.projection]
  rw [← Category.assoc, ← Functor.map_comp]
  have h : nerveMap φ.mapElements ≫ nerveMap (Functor.Elements.π Y) =
      nerveMap (Functor.Elements.π X) := by
    change nerveMap (φ.mapElements ⋙ Functor.Elements.π Y) = _
    rw [NatTrans.mapElements_comp_π]
  rw [h]

/-- 重みの射に沿って制限した錐。 -/
def restrictSectionsCone (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (elementsMap φ)).val,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c (elementsMap φ)).property.trans (elementsMap_diagram φ F)⟩

/-- 錐の制限は頂点を変えない。 -/
lemma restrictSectionsCone_vertex (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F)) :
    (restrictSectionsCone φ F c).vertex = c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone_vertex c (elementsMap φ)

/-- 制限した錐から指定された極限錐への普遍辺。 -/
def sectionsConeMap (cX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) (hcX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cX)
    (cY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F)) :
    SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) (restrictSectionsCone φ F cY) cX :=
  SSet.Edge.ofTruncated (Classical.choice
    ((show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) cX from hcX).nonempty_edge
      (restrictSectionsCone φ F cY)))

/-- 切断への制限。向きは Γ(Y,F) → Γ(X,F)。 -/
def sectionsMap (cX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) (hcX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cX)
    (cY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F)) (_hcY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cY) :
    SSet.Edge cY.vertex cX.vertex := by
  have e := (sectionsConeMap φ F cX hcX cY).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F))
  change SSet.Edge (restrictSectionsCone φ F cY).vertex cX.vertex at e
  rw [restrictSectionsCone_vertex] at e
  exact e

/-- 普遍辺のホモトピー類は錐の圏で一意。 -/
lemma sectionsConeMap_homMk_unique [Quasicategory E]
    (cX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) (hcX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cX)
    (cY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F))
    (e : SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) (restrictSectionsCone φ F cY) cX) :
    Truncated.HomotopyCategory.homMk (sectionsConeMap φ F cX hcX cY).toTruncated =
      Truncated.HomotopyCategory.homMk e.toTruncated :=
  (show _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) cX from hcX).isTerminalHo.hom_ext _ _

/-- 極限の存在証明から選んだ錐を使う切断の制限。 -/
def sectionsMapOfHasLimit (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram X F)) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram Y F)) :
    SSet.Edge hY.choose.vertex hX.choose.vertex :=
  sectionsMap φ F hX.choose hX.choose_spec hY.choose hY.choose_spec

/-- BS の篩包含 S ↪ h_U に沿う切断の制限。 -/
def sieveSectionsMap {C : Type u} [SmallCategory C] {U : C} (S : Sieve U)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)
    (cS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram S.functor F)) (hcS : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cS)
    (cU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetWeight.diagram (yoneda.obj U) F)) (hcU : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone cU) :
    SSet.Edge cU.vertex cS.vertex :=
  sectionsMap S.functorInclusion F cS hcS cU hcU

/-- BS の S4 の生成辺に使う篩包含へのテンソル。 -/
def sieveTensorEdge {C : Type u} [SmallCategory C] {U : C} (S : Sieve U)
    [Quasicategory E] (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (M : E _⦋0⦌) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram S.functor ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor hE M))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.spaceDiagram (yoneda.obj U) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tensorSpaceFunctor hE M)) :=
  tensorWeightEdge hE M S.functorInclusion

end SetWeight
end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
