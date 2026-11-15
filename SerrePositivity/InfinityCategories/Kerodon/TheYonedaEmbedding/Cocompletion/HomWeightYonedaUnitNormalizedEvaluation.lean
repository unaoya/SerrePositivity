module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CurryHomPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity

/-!
概要：元の指定Yoneda単位の点評価を、元の共同Hom単位の固定変数制限へ戻す。
方針：既存の端点正規化付き後合成と、指定単位自身のcurry表示を使う。
規約：元の射・元の評価を保持する。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3を基礎とする
指定Yoneda左Kan比較の可逆性への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open Project.QuasicategoryAuxiliaries
open Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion

/-- 概要：指定Yoneda単位の元の前層評価は同じ共同Hom単位の始点固定制限。
方針：指定単位自身のcurry表示を一般の正規化付き評価則へ渡す。
規約：全図式の元の射の異種等式。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3のYoneda・密度への接続。 -/
lemma homWeightYonedaUnit_postcompose_evaluate_heq {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C) (a : A _⦋0⦌) :
    HEq (postcomposeFunctorHom (presheafInfinityEvaluation a) (homWeightYonedaUnit F))
      (precomposeFunctorHom
        (lift (SSet.const (ULift.up (SSet.opObjEquiv.symm a)))
          (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj A))) (functorHomBifunctorUnit F)) := by
  exact curryFunctorHom_postcompose_evaluate_of_heq
    (A := (SSet.uliftFunctor.{u + 1, u}).obj A.op)
    (B := (SSet.uliftFunctor.{u + 1, u}).obj A)
    (X := SpaceInfinity.{u})
    (f := homInfinityJointEvaluation A)
    (g := (uliftTensorIso.{u, u + 1} A.op A).inv ≫ functorHomBifunctorDiagram F F)
    (f' := yonedaInfinityMap A)
    (g' := (SSet.uliftFunctor.{u + 1, u}).map F ≫
      Project.HomotopyDiagramComparison.presheafHomWeightDiagram F)
    (functorHomBifunctorUnit F) (homWeightYonedaUnit F) rfl
    (functorHomBifunctorDiagram_curry F F).symm (homWeightYonedaUnit_heq_curry F)
    (ULift.up (SSet.opObjEquiv.symm a))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
