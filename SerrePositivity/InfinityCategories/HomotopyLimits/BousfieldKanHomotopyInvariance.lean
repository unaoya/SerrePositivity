module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiagramPathSpan
public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsKan

/-!
概要：Bousfield–Kan end は Kan 値図式の成分ごとの同値をホモトピー同値に送る。
方針：自然な path 置換で二つの成分ごとの自明 Kan fibration に分解し、end の保存性を使う。
規約：添字は任意の小圏、構造射の fibration 性は不要。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の strict な係数図式と coherent な模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：Bousfield–Kan の重み付き end の表示でも Kan 性を型クラスとして利用できる。
方針：切断模型から得た既存の Kan 性を end の定義で表示する。
規約：係数図式は任意の小圏上の Kan 値図式。
使われ方：Kerodon 7.5.3.12 の end の誘導射の圏同値判定。 -/
instance bousfieldKanWeightedSections_kanComplex (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (weightedSections (bousfieldKanWeight I) H) :=
  bousfieldKanHolim_kanComplex H

/-- 概要：Kan 値図式の成分ごとの圏同値は Bousfield–Kan end の圏同値を誘導する。
方針：path 置換の二射影が誘導する自明 Kan fibration と、切断の厳密な逆関係を使う。
規約：成分の同値の逆射の族が自然であるとは仮定しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の homotopy 極限の係数に関する同値不変性。 -/
lemma bousfieldKanMap_isQCatEquivalence {F G : I ⥤ SSet.{u}}
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G)
    (hη : ∀ i, IsQCatEquivalence (η.app i)) :
    IsQCatEquivalence (weightedSectionsMap (bousfieldKanWeight I) η) := by
  have (i : I) : TrivialKanFibration ((diagramPathProjection η).app i) :=
    equivalencePathReplacementProjection_trivialKanFibration (η.app i)
  have (i : I) : TrivialKanFibration ((diagramPathEndpoint η).app i) :=
    (hη i).equivalencePathReplacementMap_trivialKanFibration
  have := bousfieldKanMap_trivialKanFibration (diagramPathProjection η)
  have := bousfieldKanMap_trivialKanFibration (diagramPathEndpoint η)
  have : Quasicategory (weightedSections (bousfieldKanWeight I) (diagramPathReplacement η)) :=
    quasicategory_of_innerFibration
      (weightedSectionsMap (bousfieldKanWeight I) (diagramPathProjection η))
  have hp := isQCatEquivalence_of_trivialKanFibration
    (weightedSectionsMap (bousfieldKanWeight I) (diagramPathProjection η))
  have hq := isQCatEquivalence_of_trivialKanFibration
    (weightedSectionsMap (bousfieldKanWeight I) (diagramPathEndpoint η))
  have hs : IsQCatEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (diagramPathSection η)) := by
    apply hp.cancel_right
    rw [← weightedSectionsMap_comp, diagramPathSection_projection, weightedSectionsMap_id]
    exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  rw [← diagramPathSection_endpoint η, weightedSectionsMap_comp]
  exact hs.comp hq

/-- 概要：Kan 値図式の成分ごとのホモトピー同値は Bousfield–Kan end のホモトピー同値を誘導する。
方針：成分の同値を圏同値として上の比較に渡し、両側の Kan 性から実際のホモトピー逆を得る。
規約：添字の有限性や遷移の fibration 性は要求しない。
使われ方：Kerodon 7.5.3.12、7.5.4.6 の homotopy 極限の具体的な不変性。 -/
lemma bousfieldKanMap_homotopyEquivalence {F G : I ⥤ SSet.{u}}
    [∀ i, KanComplex (F.obj i)] [∀ i, KanComplex (G.obj i)] (η : F ⟶ G)
    (hη : ∀ i, IsSimplicialHomotopyEquivalence (η.app i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsMap (bousfieldKanWeight I) η) :=
  (bousfieldKanMap_isQCatEquivalence η
    (fun i ↦ (hη i).isQCatEquivalence)).isSimplicialHomotopyEquivalence

/-- 概要：Kan 値図式から weighted nerve の strict transport への自然な単位は end でも同値。
方針：単位の成分ごとの同値性に end の同値不変性を適用する。
規約：元の図式の構造射に fibration 性は要求しない。
使われ方：Kerodon 5.3.5.7、7.5.4.6 の元の係数図式の homotopy 極限の回収。 -/
lemma weightedTransportUnit_end_homotopyEquivalence (H : I ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (weightedTransportUnit H)) := by
  have (i : I) : KanComplex ((leftStrictTransportDiagram (weightedNerveProjection H)).obj i) :=
    leftStrictTransport_kanComplex (weightedNerveProjection H) i
  exact bousfieldKanMap_homotopyEquivalence (weightedTransportUnit H)
    (weightedTransportUnitComponent_homotopyEquivalence H)

end SerrePositivity.InfinityCategories.HomotopyLimits
