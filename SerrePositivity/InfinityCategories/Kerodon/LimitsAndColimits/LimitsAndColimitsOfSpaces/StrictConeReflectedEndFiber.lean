module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.StrictConePinchedDerivedFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberBasePoint

/-!
概要：三形状の strict な錐への pinched Hom と反転豊穣比較 q′ の ULift 後の導来 fiber の同値。
方針：end から切断模型への同値の逆で標準点を回収し、逆のホモトピーの辺で固定点を移す。
規約：元の非反転 q_x への移送とは区別する。厳密極限性や Hom の fibration 性は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、係数の反転と宇宙の移送の入力。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

local instance strictConeReflectedEndTargetKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) := by
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _

/-- 概要：標準の錐の切断点を end からの同値の逆で回収した反転・ULift 後の end の点。
方針：指定したホモトピー同値の逆を標準点で評価する。
規約：同値の逆の選択を含む。像と元の点の等式は要求せずホモトピーで照合する。
使われ方：反転した豊穣比較の導来 fiber の固定点。 -/
def strictConeReflectedEndPoint {F : I ⥤ C} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))) :
    ((SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex) ⋙ SSet.opFunctor))) _⦋0⦌ :=
  (Classical.choose hκ).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeDerivedFiberPoint d)

/-- 概要：end から切断への比較が同値なら pinched Hom は ULift 後の反転豊穣比較の fiber と同値。
方針：切断比較の fiber の同値に、任意の固定点を回収する標的の同値の fiber 比較を合成する。
規約：この一般形では end 比較の同値性を入力に取る。三形状では後続の公開定理で検証する。
使われ方：HTT 4.2.4.1、元の非反転 q_x への直接比較の中間段階。 -/
def strictConePinched_reflectedEndDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d hκ)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConePinched_reflectedDerivedFiberEquivalence c d
  let e' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPostInverseEquivalence
    ((SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)) hκ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeDerivedFiberPoint d)
  exact e.trans e'.symm

/-- 概要：discrete の strict な錐への pinched Hom と ULift 後の反転豊穣比較の fiber は同値。
方針：この形状の end から切断への実際の比較の同値性を一般の fiber 比較へ渡す。
規約：局所 Kan 性だけを要求し、通常の錐 c と coherent な錐 d は任意。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber へ向かう反転側の比較。 -/
def strictConePinched_reflectedEnd_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))) :=
  strictConePinched_reflectedEndDerivedFiberEquivalence c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))

/-- 概要：cospan の strict な錐への pinched Hom と ULift 後の反転豊穣比較の fiber は同値。
方針：この形状の end から切断への実際の比較の同値性を一般の fiber 比較へ渡す。
規約：局所 Kan 性だけを要求し、通常の錐 c と coherent な錐 d は任意。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber へ向かう反転側の比較。 -/
def strictConePinched_reflectedEnd_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence F
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))) :=
  strictConePinched_reflectedEndDerivedFiberEquivalence c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))

/-- 概要：tower の strict な錐への pinched Hom と ULift 後の反転豊穣比較の fiber は同値。
方針：この形状の end から切断への実際の比較の同値性を一般の fiber 比較へ渡す。
規約：局所 Kan 性だけを要求し、通常の錐 c と coherent な錐 d は任意。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber へ向かう反転側の比較。 -/
def strictConePinched_reflectedEnd_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber ((SSet.uliftFunctor.{v, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))
        (strictConeReflectedEndPoint d
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex)))) :=
  strictConePinched_reflectedEndDerivedFiberEquivalence c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
