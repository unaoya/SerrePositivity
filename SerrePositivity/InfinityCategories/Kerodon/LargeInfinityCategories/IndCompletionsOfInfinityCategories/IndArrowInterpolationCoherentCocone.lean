module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationSquareTip

/-!
概要：帰還した全変換を、元の指定区間図式を頂点とする coherent な全余錐にする。
方針：全円柱の両側を保持したまま因子を交換し、内部 Hom の随伴で curry する。
規約：まだ C 図式の小さい表示への降下は行わない。使われ方：元の図式 comma への帰還。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D}
  (V : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowInterpolationData κ D q)

/-- 延長された元の C 図式を、標準区間の全 coherent 関手族として読む。 -/
def indArrowInterpolationCoherentDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj ((SSet.uliftFunctor.{u + 1, u}).obj C) :=
  curry ((β_ Δ[1] _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationDiagram V)

/-- 元の Ind 内の全変換を、そのまま全余錐の射として curry する。 -/
def indArrowInterpolationCoherentCoconeMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))) Δ[0] ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) :=
  curry ((β_ Δ[1] _).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSquare V)

/-- 元の C 全図式の Yoneda 像に、coherent な全余錐が厳密に制限される。 -/
lemma indArrowInterpolationCoherentCoconeMap_old :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))) Δ[0] ≫
      indArrowInterpolationCoherentCoconeMap V =
        indArrowInterpolationCoherentDiagram V ≫
          (ihom (Δ[1] : SSet.{u + 1})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))
  apply uncurry_injective
  rw [indArrowInterpolationCoherentCoconeMap, uncurry_natural_left, uncurry_curry,
    uncurry_natural_right, indArrowInterpolationCoherentDiagram, uncurry_curry]
  have h : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B (Δ[0] : SSet.{u + 1})) ≫ (β_ Δ[1] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B Δ[0])).hom =
      (β_ Δ[1] B).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B Δ[0] ▷ Δ[1]) := by rfl
  simpa only [B, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSquare_old V] using
    congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSquare V) h

/-- 元の C 全図式の Yoneda 像に対する実際の全 coherent 余錐。 -/
def indArrowInterpolationCoherentCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (indArrowInterpolationCoherentDiagram V ≫
      (ihom (Δ[1] : SSet.{u + 1})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)) :=
  ⟨indArrowInterpolationCoherentCoconeMap V, indArrowInterpolationCoherentCoconeMap_old V⟩

/-- 余錐の全頂点図式は、元の同じ指定区間図式の標準区間表示。 -/
lemma indArrowInterpolationCoherentCoconeMap_tip :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))) Δ[0] ≫
      indArrowInterpolationCoherentCoconeMap V =
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall.{u} ≫ D)) := by
  let B := (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}))
  apply uncurry_injective
  rw [indArrowInterpolationCoherentCoconeMap, uncurry_natural_left, uncurry_curry,
    SSet.yonedaEquiv_symm_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  have h : (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B (Δ[0] : SSet.{u + 1})) ≫ (β_ Δ[1] (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B Δ[0])).hom =
      (β_ Δ[1] Δ[0]).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr B Δ[0] ▷ Δ[1]) := by rfl
  simpa only [B, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSquare_tip V, braiding_hom_snd_assoc] using
    congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indArrowInterpolationSquare V) h

/-- この全 coherent 余錐の頂点は同じ元の指定図式の標準区間表示そのもの。 -/
lemma indArrowInterpolationCoherentCocone_vertex :
    (indArrowInterpolationCoherentCocone V).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall.{u} ≫ D) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, show (indArrowInterpolationCoherentCocone V).val =
    indArrowInterpolationCoherentCoconeMap V from rfl,
    indArrowInterpolationCoherentCoconeMap_tip, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
