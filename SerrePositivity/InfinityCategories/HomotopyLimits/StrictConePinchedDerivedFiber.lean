module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ComparisonFiberIndex
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeRestrictionDerivedFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeDerivedFiberComparison

/-!
概要：strict な錐への pinched Hom と反転・ULift 後の切断比較の導来 fiber の直接の同値。
方針：native な制限の fiber の同値を weighted な錐全体の実際の fiber 比較の逆と合成する。
規約：元の非反転 q_x とは区別する。底の点は任意の coherent な錐 d の標準の切断の点。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、元の比較への反転と宇宙の移送の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：任意の coherent な錐の標準の切断の点を、その頂点が表す元の対象で表示する。
方針：coherent nerve の零単体の対象との全単射の逆関係で頂点を移送する。
規約：選んだ切断比較の像ではなく元の錐 d の標準の点を使う。
使われ方：反転・ULift 後の豊穣 Hom の比較の導来 fiber の固定点。 -/
def strictConeDerivedFiberPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F)) :
    (coherentConeSectionSpace (strictCoherentDiagram F)
      (coherentNerveVertex (coherentNerveObject d.vertex))) _⦋0⦌ :=
  (coherentNerveVertex_object d.vertex).symm ▸ coherentConeSectionPoint d

/-- 概要：strict な錐への pinched Hom は反転・ULift 後の切断比較の導来 fiber と同値。
方針：native な制限の fiber との同値を頂点の表示で移送し、weighted な fiber 比較を逆に使う。
規約：添字圏と通常の錐 c、比較する coherent な錐 d は任意。局所 Kan 性のみを要求する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6・7.5.4.6、元の非反転 q_x の fiber への直接比較。 -/
def strictConePinched_reflectedDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      (comparisonFiber (reflectedStrictConeSectionsComparison c (coherentNerveObject d.vertex))
        (strictConeDerivedFiberPoint d)) := by
  let e := conePinchedHom_sectionRestrictionDerivedFiberEquivalence d (strictCoherentCone c)
  let e' := comparisonFiberIndexIso
    (fun z ↦ coherentConeSectionSpace (strictCoherentCone c).val z)
    (fun z ↦ coherentConeSectionSpace (strictCoherentDiagram F) z)
    (coneSectionRestriction (strictCoherentCone c)) (coherentNerveVertex_object d.vertex).symm
    (coherentConeSectionPoint d)
  exact (e.trans (qCatEquivalenceOfIso e')).trans
    (weightedStrictConeFamilyFiberComparison_homotopyEquivalence c (coherentNerveObject d.vertex)
      (strictConeDerivedFiberPoint d)).isQCatEquivalence.choose.symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
