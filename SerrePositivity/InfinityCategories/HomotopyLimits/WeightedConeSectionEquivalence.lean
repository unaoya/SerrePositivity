module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LiftedShapeNerveIso

/-!
概要：積・cospan・塔の反転豊穣係数の切断と coherent な錐の切断は同値。
方針：持ち上げた底を標準形状へ同型で移し、実際の全 fiber の同値性を切断へ移す。
規約：実際の weightedCoherentConeSectionsComparison の同値性を証明する。
使われ方：HTT 4.2.4.1、Kerodon §7.5.4 の豊穣 Hom の極限と coherent な錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：離散図式の反転豊穣係数の実際の切断比較射はホモトピー同値。
方針：底の同型と各 fiber の同値性から三形状の切断判定を使い、錐の切断模型へ移す。
規約：局所 Kan 性以外に図式の射や極限の条件を追加しない。
使われ方：HTT 4.2.4.1 の 離散図式の錐の写像空間の比較。 -/
lemma weightedCoherentConeSectionsComparison_discrete_homotopyEquivalence {J : Type u}
    (F : (Discrete J) ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x) := by
  have := simplicialSections_kanComplex ((SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
  have := simplicialSections_kanComplex
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
  have hs := simplicialSectionsMap_discreteBaseIso_homotopyEquivalence
    ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
    (liftedDiscreteNerveIso.{u, v} J)
    (weightedCoherentConeComparison F x) (weightedCoherentConeComparison_over F x)
    (fun b ↦ weightedCoherentConeFiberMap_homotopyEquivalence F x b)
  have ht := (qCatEquivalenceOfIso
    (coherentConeSectionsIso (strictCoherentDiagram F) (coherentNerveVertex x))).isQCatEquivalence
  exact hs.comp ht.isSimplicialHomotopyEquivalence

/-- 概要：cospanの反転豊穣係数の実際の切断比較射はホモトピー同値。
方針：底の同型と各 fiber の同値性から三形状の切断判定を使い、錐の切断模型へ移す。
規約：局所 Kan 性以外に図式の射や極限の条件を追加しない。
使われ方：HTT 4.2.4.1 の cospanの錐の写像空間の比較。 -/
lemma weightedCoherentConeSectionsComparison_cospan_homotopyEquivalence
    (F : (AsSmall.{u} WalkingCospan) ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x) := by
  have := simplicialSections_kanComplex ((SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
  have := simplicialSections_kanComplex
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
  have hs := simplicialSectionsMap_cospanBaseIso_homotopyEquivalence
    ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
    (liftedAsSmallNerveIso.{u, v} WalkingCospan)
    (weightedCoherentConeComparison F x) (weightedCoherentConeComparison_over F x)
    (fun b ↦ weightedCoherentConeFiberMap_homotopyEquivalence F x b)
  have ht := (qCatEquivalenceOfIso
    (coherentConeSectionsIso (strictCoherentDiagram F) (coherentNerveVertex x))).isQCatEquivalence
  exact hs.comp ht.isSimplicialHomotopyEquivalence

/-- 概要：塔の反転豊穣係数の実際の切断比較射はホモトピー同値。
方針：底の同型と各 fiber の同値性から三形状の切断判定を使い、錐の切断模型へ移す。
規約：局所 Kan 性以外に図式の射や極限の条件を追加しない。
使われ方：HTT 4.2.4.1 の 塔の錐の写像空間の比較。 -/
lemma weightedCoherentConeSectionsComparison_tower_homotopyEquivalence
    (F : (AsSmall.{u} ℕᵒᵖ) ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x) := by
  have := simplicialSections_kanComplex ((SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
  have := simplicialSections_kanComplex
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
  have hs := simplicialSectionsMap_towerBaseIso_homotopyEquivalence
    ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
    (liftedAsSmallNerveIso.{u, v} ℕᵒᵖ)
    (weightedCoherentConeComparison F x) (weightedCoherentConeComparison_over F x)
    (fun b ↦ weightedCoherentConeFiberMap_homotopyEquivalence F x b)
  have ht := (qCatEquivalenceOfIso
    (coherentConeSectionsIso (strictCoherentDiagram F) (coherentNerveVertex x))).isQCatEquivalence
  exact hs.comp ht.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
