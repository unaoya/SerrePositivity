module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.DiagramPathSpan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan

/-!
概要：Bousfield–Kan end は Kan 値図式の成分ごとの同値をホモトピー同値に送る。
方針：自然な path 置換で二つの成分ごとの自明 Kan fibration に分解し、end の保存性を使う。
規約：添字は任意の小圏、構造射の fibration 性は不要。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の strict な係数図式と coherent な模型の比較。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {I : Type u} [SmallCategory I]

/-- 概要：Bousfield–Kan の重み付き end の表示でも Kan 性を型クラスとして利用できる。
方針：切断模型から得た既存の Kan 性を end の定義で表示する。
規約：係数図式は任意の小圏上の Kan 値図式。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の end の誘導射の圏同値判定。 -/
instance bousfieldKanWeightedSections_kanComplex (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) H) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H

/-- 概要：Kan 値図式の成分ごとの圏同値は Bousfield–Kan end の圏同値を誘導する。
方針：path 置換の二射影が誘導する自明 Kan fibration と、切断の厳密な逆関係を使う。
規約：成分の同値の逆射の族が自然であるとは仮定しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の homotopy 極限の係数に関する同値不変性。 -/
lemma bousfieldKanMap_isQCatEquivalence {F G : I ⥤ SSet.{u}}
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η) := by
  have (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathProjection η).app i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection_trivialKanFibration (η.app i)
  have (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathEndpoint η).app i) :=
    (hη i).equivalencePathReplacementMap_trivialKanFibration
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathProjection η)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanMap_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathEndpoint η)
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacement η)) :=
    quasicategory_of_innerFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathProjection η))
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathProjection η))
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathEndpoint η))
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection η)) := by
    apply hp.cancel_right
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_id]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection_endpoint η, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_comp]
  exact hs.comp hq

/-- 概要：Kan 値図式の成分ごとのホモトピー同値は Bousfield–Kan end のホモトピー同値を誘導する。
方針：成分の同値を圏同値として上の比較に渡し、両側の Kan 性から実際のホモトピー逆を得る。
規約：添字の有限性や遷移の fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の homotopy 極限の具体的な不変性。 -/
lemma bousfieldKanMap_homotopyEquivalence {F G : I ⥤ SSet.{u}}
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G)
    (hη : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (η.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) η) :=
  (bousfieldKanMap_isQCatEquivalence η
    (fun i ↦ (hη i).isQCatEquivalence)).isSimplicialHomotopyEquivalence

/-- 概要：Kan 値図式から weighted nerve の strict transport への自然な単位は end でも同値。
方針：単位の成分ごとの同値性に end の同値不変性を適用する。
規約：元の図式の構造射に fibration 性は要求しない。
使われ方：Kerodon 5.3.5.7（Tag 037Q）、7.5.4.6（Tag 03BB） の元の係数図式の homotopy 極限の回収。 -/
lemma weightedTransportUnit_end_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedTransportUnit H)) := by
  have (i : I) : KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H)).obj i) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H) i
  exact bousfieldKanMap_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedTransportUnit H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedTransportUnitComponent_homotopyEquivalence H)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
