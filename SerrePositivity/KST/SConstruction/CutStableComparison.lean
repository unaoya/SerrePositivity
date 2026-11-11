module
public import SerrePositivity.KST.SConstruction.CutEvaluationOperators
public import SerrePositivity.KST.SConstruction.CofiberPreservesPushout

/-! # 切断 cofiber 比較の完全性と中央の回収
概要：任意の切断位置の比較を完全関手にし、中央評価が元の恒等関手であることを示す。
方針：全角の元の S_n の制限による評価式で完全性を点ごとに確認する。
規約：左右への分解の同値性は後続で証明する。使われ方：Segal 分解の相対 cofiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 切断 cofiber 比較は零対象と cofiber を保存する。 -/
lemma cutCofiberComparison_preservesCofiberData (n : ℕ) (k : Fin (n + 1)) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] : PreservesCofiberData (cutCofiberComparison n k C) := by
  apply preservesCofiberData_fullSubcomplex_of_comp IsCofiberDiagramVertex
  apply PreservesSConstructionData.toCofiberData
  apply preservesSConstructionData_functor_of_pointwise
  rintro ⟨x, y⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  change PreservesSConstructionData (cutCofiberComparison n k C ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)
  rw [cutCofiberComparison_evaluation]
  exact (preservesCofiberData_sMap C (cutCornerOrder k i j)).toSConstructionData

/-- 元の同じ S_n C 内の切断 cofiber 四角形への完全関手。 -/
def cutStableComparison (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    sStableModel n X ⟶ cofiberStableModel (sStableModel n X) :=
  ⟨cutCofiberComparison n k X.carrier,
    cutCofiberComparison_preservesCofiberData n k X.carrier⟩

/-- 完全な切断比較の全角の評価は元の端点制限の完全関手。 -/
lemma cutStableComparison_evaluation (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u})
    (x y : Fin 2) :
    cutStableComparison n k X ≫ cofiberStableEvaluation (sStableModel n X)
        (stdSimplex.obj₀Equiv.symm x, stdSimplex.obj₀Equiv.symm y) =
      ⟨sMap X.carrier (cutCornerOrder k x y),
        preservesCofiberData_sMap X.carrier (cutCornerOrder k x y)⟩ :=
  Subtype.ext (cutCofiberComparison_evaluation n k X.carrier x y)

/-- 切断四角形の中央の端点写像は恒等写像。 -/
lemma cutCornerOrder_one_zero {n : ℕ} (k : Fin (n + 1)) :
    cutCornerOrder k 1 0 = (OrderHom.id : Fin (n + 1) →o _) := by
  exact DFunLike.ext _ _ (fun i => cutEndpoint_one_zero k i)

/-- 完全な切断 cofiber 比較の中央評価は元の S_n C の恒等関手を厳密に回収する。 -/
lemma cutStableComparison_middle (n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    cutStableComparison n k X ≫ cofiberStableMiddle (sStableModel n X) =
      𝟙 (sStableModel n X) := by
  apply Subtype.ext
  change cutCofiberComparison n k X.carrier ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
  rw [cutCofiberComparison_evaluation, cutCornerOrder_one_zero, sMap_id]
  rfl

end SerrePositivity.KST.SConstruction
