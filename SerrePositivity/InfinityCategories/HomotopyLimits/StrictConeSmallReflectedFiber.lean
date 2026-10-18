module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseComparisonFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeReflectedEndFiber

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

local instance strictConeSmallReflectedTargetKan
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) :
    KanComplex (bousfieldKanHolim (simplicialHomDiagram F x ⋙ SSet.opFunctor)) := by
  have : ∀ i, KanComplex ((simplicialHomDiagram F x ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom x (F.obj i)).op)
  exact bousfieldKanHolim_kanComplex _

/-- 概要：coherent な錐の標準点から回収した反転 end の点を元の宇宙へ戻す。
方針：選んだ比較同値の逆による ULift の点から ULift.down を取る。
規約：固定点の選択と path による照合は既存の反転 end の比較と同じ。
使われ方：元の宇宙の q′ の導来 fiber の固定点。 -/
def strictConeSmallReflectedEndPoint {F : I ⥤ C} (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex))) :
    (bousfieldKanHolim
      (simplicialHomDiagram F (coherentNerveObject d.vertex) ⋙ SSet.opFunctor)) _⦋0⦌ :=
  (strictConeReflectedEndPoint d hκ).down

/-- 概要：end 比較が同値なら pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：既存の反転 end の fiber の同値に、導来 fiber と ULift の標準同型の逆を合成する。
規約：一般形の hκ は明示する。ULift は比較射の内部から fiber 全体の外へ移る。
使われ方：HTT 4.2.4.1、元の非反転 q_x の fiber への反転の移送。 -/
def strictConePinched_smallReflectedEndDerivedFiberEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : I ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F))
    (hκ : IsSimplicialHomotopyEquivalence
      (reflectedHomHolimConeComparison F (coherentNerveObject d.vertex))) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d hκ))) := by
  let e := strictConePinched_reflectedEndDerivedFiberEquivalence c d hκ
  let e' := uliftComparisonFiberIso.{u, v}
    (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
    (strictConeSmallReflectedEndPoint d hκ)
  exact e.trans (qCatEquivalenceOfIso e'.symm)

/-- 概要：discrete の錐への pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：この形状の end 比較の同値性を一般の宇宙を戻した fiber 比較へ渡す。
規約：局所 Kan 性のみを要求し、c の極限性や Hom の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber と直接比較するための反転側の模型。 -/
def strictConePinched_smallReflectedEnd_discrete_equivalence {J : Type u}
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (Discrete J) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F
              (coherentNerveObject d.vertex))))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_discrete_homotopyEquivalence F (coherentNerveObject d.vertex))

/-- 概要：cospan の錐への pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：この形状の end 比較の同値性を一般の宇宙を戻した fiber 比較へ渡す。
規約：局所 Kan 性のみを要求し、c の極限性や Hom の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber と直接比較するための反転側の模型。 -/
def strictConePinched_smallReflectedEnd_cospan_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} WalkingCospan) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (reflectedHomHolimConeComparison_cospan_homotopyEquivalence F
              (coherentNerveObject d.vertex))))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_cospan_homotopyEquivalence F (coherentNerveObject d.vertex))

/-- 概要：tower の錐への pinched Hom は元の宇宙の反転比較の導来 fiber の ULift と同値。
方針：この形状の end 比較の同値性を一般の宇宙を戻した fiber 比較へ渡す。
規約：局所 Kan 性のみを要求し、c の極限性や Hom の fibration 性は要求しない。
使われ方：HTT 4.2.4.1、三形状の元の q_x の fiber と直接比較するための反転側の模型。 -/
def strictConePinched_smallReflectedEnd_tower_equivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)]
    {F : (AsSmall.{u} ℕᵒᵖ) ⥤ C} (c : Cone F) (d : JoinCone (strictCoherentDiagram F)) :
    QCatEquivalence
      (pinchedHom (X := sliceOver (strictCoherentDiagram F)) d (strictCoherentCone c))
      ((SSet.uliftFunctor.{v, u}).obj
        (comparisonFiber (reflectedRepresentableComparison c (coherentNerveObject d.vertex))
          (strictConeSmallReflectedEndPoint d
            (reflectedHomHolimConeComparison_tower_homotopyEquivalence F
              (coherentNerveObject d.vertex))))) :=
  strictConePinched_smallReflectedEndDerivedFiberEquivalence c d
    (reflectedHomHolimConeComparison_tower_homotopyEquivalence F (coherentNerveObject d.vertex))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
