module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：同じ全関手間の二胞体の成分は、元の指定辺のホモトピー類と可換する。
方針：既存のホモトピー圏の自然変換の自然性を、その成分評価の式で書き直す。
規約：HTT §1.2.3、Kerodon §4.4（Tag 01EM）の既存の評価の法則。
使われ方：S8 の全体で構成した右 Kan 比較を、元の指定重みの辺で評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 同じ二胞体の成分は、指定辺を元の二つの全関手で写した類と可換する。 -/
lemma functorHomEvaluate_edge_naturality {A X : SSet.{u}} [Quasicategory X]
    {F G : A ⟶ X} (α : FunctorHom F G) {x y : A _⦋0⦌} (a : SSet.Edge x y) :
    Truncated.HomotopyCategory.homMk (a.map F).toTruncated ≫ functorHomEvaluate α y =
      functorHomEvaluate α x ≫ Truncated.HomotopyCategory.homMk (a.map G).toTruncated := by
  have h := (functorCellToNatTrans α).naturality
    (Truncated.HomotopyCategory.homMk a.toTruncated)
  rw [← functorCellToNatTrans_app_eq_evaluate (A := A) (X := X) α y,
    ← functorCellToNatTrans_app_eq_evaluate (A := A) (X := X) α x]
  exact h

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
