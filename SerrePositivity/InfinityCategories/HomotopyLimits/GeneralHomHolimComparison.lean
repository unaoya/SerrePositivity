module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SectionsFiberwiseEquivalence
public import SerrePositivity.InfinityCategories.F1.UniverseInnerFibration
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedHomHolimComparison

/-!
概要：任意の小圏上で反転豊穣 Hom の end と coherent な錐の切断模型を比較する。
方針：実際の全 fiber の同値性を一般の切断判定へ渡し、end の標準同型を合成する。
規約：局所 Kan 性だけを仮定し、添字の形状や Hom の遷移の充填性を要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の一般形状の極限比較と余極限への双対化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]

/-- 概要：任意の小圏上の反転豊穣係数の切断比較射はホモトピー同値。
方針：各 fiber の同値性から切断への実際の後合成の同値性を得て、錐の模型を同型で移す。
規約：添字圏の有限性や射の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の一般形状の錐の比較。 -/
lemma weightedCoherentConeSectionsComparison_homotopyEquivalence (F : I ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (weightedCoherentConeSectionsComparison F x) := by
  have := simplicialSections_kanComplex ((SSet.uliftFunctor.{v, u}).map
    (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
  have := simplicialSections_kanComplex
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
  have hs := simplicialSectionsMap_homotopyEquivalence_of_fibers
    ((SSet.uliftFunctor.{v, u}).map
      (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor)))
    (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex x))
    (weightedCoherentConeComparison F x) (weightedCoherentConeComparison_over F x)
    (fun b ↦ (weightedCoherentConeFiberMap_homotopyEquivalence F x b).isQCatEquivalence)
  have ht := (qCatEquivalenceOfIso
    (coherentConeSectionsIso (strictCoherentDiagram F) (coherentNerveVertex x))).isQCatEquivalence
  exact hs.comp ht.isSimplicialHomotopyEquivalence

/-- 概要：任意の小圏上の反転豊穣 Hom の end から coherent な錐への比較射は同値。
方針：end の切断表示と ULift の交換同型に一般の切断比較を合成する。
規約：元の非反転係数の比較との同定は別の段階とする。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6 の一般の極限判定。 -/
lemma reflectedHomHolimConeComparison_homotopyEquivalence (F : I ⥤ C) (x : C) :
    IsSimplicialHomotopyEquivalence (reflectedHomHolimConeComparison F x) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  have := bousfieldKanHolim_kanComplex (simplicialHomDiagram F x ⋙ SSet.opFunctor)
  have := weightedConeSourceSections_kanComplex F x
  have he := QCatEquivalence.isQCatEquivalence (qCatEquivalenceOfIso
    ((SSet.uliftFunctor.{v, u}).mapIso
        (bousfieldKanSectionsIso (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≪≫
      uliftSectionsIso (weightedNerveProjection (simplicialHomDiagram F x ⋙ SSet.opFunctor))))
  exact he.isSimplicialHomotopyEquivalence.comp
    (weightedCoherentConeSectionsComparison_homotopyEquivalence F x)

end SerrePositivity.InfinityCategories.HomotopyLimits
