module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialBoundaryCalculus
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary

/-!
概要：相対余錐の充填条件と底の余極限性から絶対的な余極限性を回収する。
方針：底の余錐制限の境界充填を引き戻し、相対比較の境界充填と合成する。
規約：U が余極限を保存することは仮定せず、指定した余錐の像の余極限性を要求する。
使われ方：相対 Kan の局所普遍性と既存の絶対的な余極限 API の接続。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐全体を標的の関手で後合成する。
方針：余錐の射に U を合成し、固定図式の条件も後合成する。
規約：像の図式は p≫U。
使われ方：底における指定余錐の普遍性の記述。 -/
def kanPostcomposeCocone {K D E : SSet.{u}} (U : D ⟶ E) {p : K ⟶ D}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ U) :=
  ⟨c.val ≫ U, by rw [← Category.assoc, c.property]⟩

/-- 概要：相対余錐の充填条件と像の余極限性から元の余極限性が従う。
方針：底の余錐の始点境界充填を第一射影へ引き戻し、相対余錐制限の条件と合成する。
規約：U の fibration 性は不要。D と E は quasicategory。
使われ方：相対的な構成から通常の Kan 条件へ戻す。 -/
lemma kanIsColimitCone_of_relativeLifting_of_image {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) {p : K ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U c) (himage : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (kanPostcomposeCocone U c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val)
  have he : (pullback.snd ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)).app (Opposite.op ⦋0⦌) x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (kanPostcomposeCocone U c).val := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U ≫
      pullback.snd ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)).app
        (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_snd]
    rfl
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting
      (pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)) x := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialBoundaryLifting_pullback_fst
    rw [he]
    exact himage.initialBoundaryLifting
  have hcomp := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialBoundaryLifting_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction K U)
    (pullback.fst ((ihom K).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) hc hx
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_fst] at hcomp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction c hcomp

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
