module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseComparisonFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.StrictConeReflectedEndFiber

/-!
概要：strict な錐への pinched Hom を元の宇宙の反転比較 q′ の導来 fiber の ULift と同定する。
方針：導来 fiber と ULift の標準同型で既存の三形状の比較から ULift を外へ移す。
規約：pinched Hom と宇宙を揃える ULift は fiber 全体に残す。反転の除去は後続工程。
使われ方：HTT 4.2.4.1、元の非反転 q_x への反転の移送の入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

local instance strictConeSmallReflectedTargetKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)) := by
  have : ∀ i, KanComplex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex _

/-- 概要：coherent な錐の標準点から回収した反転 end の点を元の宇宙へ戻す。
方針：選んだ比較同値の逆による ULift の点から ULift.down を取る。
規約：固定点の選択と path による照合は既存の反転 end の比較と同じ。
使われ方：元の宇宙の q′ の導来 fiber の固定点。 -/
def strictConeSmallReflectedEndPoint {F : I ⥤ C} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex) ⋙ SSet.opFunctor)) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConeReflectedEndPoint d hκ).down

/-- 概要：end 比較が同値なら pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：既存の反転 end の fiber の同値に、導来 fiber と ULift の標準同型の逆を合成する。
規約：一般形の hκ は明示する。ULift は比較射の内部から fiber 全体の外へ移る。
使われ方：HTT 4.2.4.1、元の非反転 q_x の fiber への反転の移送。 -/
def strictConePinched_smallReflectedEndDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F))
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d hκ))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.strictConePinched_reflectedEndDerivedFiberEquivalence c d hκ
  let e' := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftComparisonFiberIso.{u, v}
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
    (strictConeSmallReflectedEndPoint d hκ)
  exact e.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e'.symm)

/-- 概要：discrete の錐への pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：この形状の end 比較の同値性を一般の宇宙を戻した fiber 比較へ渡す。
規約：局所 Kan 性のみを要求し、c の極限性や Hom の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber と直接比較するための反転側の模型。 -/
def strictConePinched_smallReflectedEnd_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_discrete_homotopyEquivalence F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))

/-- 概要：cospan の錐への pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：この形状の end 比較の同値性を一般の宇宙を戻した fiber 比較へ渡す。
規約：局所 Kan 性のみを要求し、c の極限性や Hom の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber と直接比較するための反転側の模型。 -/
def strictConePinched_smallReflectedEnd_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence F
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_cospan_homotopyEquivalence F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))

/-- 概要：tower の錐への pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：この形状の end 比較の同値性を一般の宇宙を戻した fiber 比較へ渡す。
規約：局所 Kan 性のみを要求し、c の極限性や Hom の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber と直接比較するための反転側の模型。 -/
def strictConePinched_smallReflectedEnd_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)) d (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedRepresentableComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedHomHolimConeComparison_tower_homotopyEquivalence F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject d.vertex))

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
