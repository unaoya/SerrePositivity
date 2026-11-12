module
public import SerrePositivity.KST.ProExcision.IntegerLinearizationAdjunction
public import SerrePositivity.KST.ProExcision.ModuleHomologySequentialColimits
public import SerrePositivity.KST.ProExcision.HomologyReversal
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# 借用する H_* の自然な鎖模型から得る順序余極限の実比較

概要：既存の自然な複体模型を持つ H_* が順序余極限を保存することを実証明する。
方針：自由整数複体の次数ごとの保存と、K-L2 から移した実ホモロジー保存を合成する。
規約：KST Proposition 4.14、SW92 Lemma 1.4。filtered 保存を新しい入力にしない。
使われ方：安定モノイドの H_* と有限 rank の H_* の実余極限の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Limits HomologicalComplex Opposite
open scoped Simplicial

/-- 概要：実自由整数鎖複体の次数評価は単体次数の実自由化と自然に同型。
方針：交代面写像複体の次数の実定義を評価する。
規約：KST App. A。使われ方：実鎖模型の余極限保存の判定。 -/
def linearizedChainEvaluationIso (n : ℕ) :
    linearizedChainFunctor.{u} ⋙ HomologicalComplex.eval (ModuleCat.{u} ℤ) (.down ℕ) n ≅
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- 概要：実自由整数鎖複体は順序余極限を保存する。
方針：各次数の実自由化と単体評価の余極限保存で判定する。
規約：SW92 Lemma 1.4。使われ方：実 H_* の順序余極限比較。 -/
instance linearizedChainFunctor_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ linearizedChainFunctor.{u} :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n ↦
    preservesColimitsOfShape_of_natIso (linearizedChainEvaluationIso n).symm)

/-- 概要：自然な実複体模型を持つ借用 H_* は順序余極限を保存する。
方針：実鎖模型と実ホモロジー保存を合成し、既存の模型自然同型で戻す。
規約：KST Proposition 4.14、SW92 Lemma 1.4。保存性を追加の仮定にしない。
使われ方：安定 H_* と有限 rank の H_* の実比較。 -/
lemma SimplicialHomologyModel.preservesSequentialColimits
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i) :
    PreservesColimitsOfShape ℕ F :=
  preservesColimitsOfShape_of_natIso M.toNatIso.symm

/-- 概要：借用する H_* と実順序余極限の標準の実同型。
方針：自然な実鎖模型から証明した保存性を標準比較に供給する。
規約：SW92 Lemma 1.4。使われ方：有限 rank の実零化を安定 H_* へ移す。 -/
def SimplicialHomologyModel.sequentialColimitIso
    {F : SSet.{u} ⥤ ModuleCat.{u} ℤ} {i : ℕ} (M : SimplicialHomologyModel F i)
    (D : ℕ ⥤ SSet.{u}) : F.obj (colimit D) ≅ colimit (D ⋙ F) := by
  letI := M.preservesSequentialColimits
  exact preservesColimitIso F D

end SerrePositivity.KST.ProExcision
