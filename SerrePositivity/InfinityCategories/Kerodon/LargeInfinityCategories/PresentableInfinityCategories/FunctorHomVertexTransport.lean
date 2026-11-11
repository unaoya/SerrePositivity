module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import Mathlib.CategoryTheory.HomCongr

/-!
概要：全関手圏の頂点間の射を、指定した元の関手間の Hom として表示する。
方針：頂点の等式による Hom 共役を使う。
規約：射も評価点も変更しない。
使われ方：全余錐の頂点比較を指定した有限余積関手の比較へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：頂点間の元の射を指定関手間の Hom へ輸送する。
方針：両端の等式の同型で共役する。
規約：元の射を保持する。
使われ方：有限余積の全比較の表示。 -/
def functorHomOfVertexEq {A X : SSet.{u}} {x y : ((ihom A).obj X) _⦋0⦌}
    (α : (HomotopyCategory.mk x : hoFunctor.obj ((ihom A).obj X)) ⟶ HomotopyCategory.mk y)
    {F G : A ⟶ X} (hx : x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (hy : y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G :=
  Iso.homCongr (eqToIso (congrArg HomotopyCategory.mk hx))
    (eqToIso (congrArg HomotopyCategory.mk hy)) α

/-- 概要：頂点表示を輸送した射の各点での可逆性は元の評価の可逆性と同値。
方針：評価後の両端の等式による同型を相殺する。
規約：同じ指定評価点を使う。
使われ方：余錐比較の各点の可逆性の反映。 -/
lemma functorHomOfVertexEq_evaluate_isIso_iff {A X : SSet.{u}}
    {x y : ((ihom A).obj X) _⦋0⦌}
    (α : (HomotopyCategory.mk x : hoFunctor.obj ((ihom A).obj X)) ⟶ HomotopyCategory.mk y)
    {F G : A ⟶ X} (hx : x = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (hy : y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) (a : A _⦋0⦌) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (functorHomOfVertexEq α hx hy) a) ↔
      IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor.map α) := by
  simp only [functorHomOfVertexEq, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate, Iso.homCongr_apply,
    eqToIso.inv, eqToIso.hom, CategoryTheory.Functor.map_comp, eqToHom_map]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
