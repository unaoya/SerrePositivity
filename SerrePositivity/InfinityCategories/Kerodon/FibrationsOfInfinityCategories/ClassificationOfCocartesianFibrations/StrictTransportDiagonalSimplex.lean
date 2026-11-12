module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalRelativeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UnderNerveDiagram

/-!
概要：底の射列と left fibrations の coherent 単体から作る strict transport の対角単体。
方針：射列上の undercategory の反変図式を作り、二つの図式の対角評価を適用する。
規約：通常の射列は小さい Fin、coherent な thickening は同じ Fin の ULift を用いる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手の二変数の評価の単体。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底の射列上の undercategory の nerve の反変図式。
方針：持ち上げた有限順序を元へ戻し、射列と underNerveDiagram を合成する。
規約：coherent nerve の thickening と同じ宇宙 u の有限順序を始域にする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類の評価単体の底の図式。 -/
def strictTransportSimplexUnderDiagram {C : Type u} [Category.{u} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : (ULift.{u} (Fin (n + 1)))ᵒᵖ ⥤ Over (nerve C) :=
  (((⟨ULift.down, fun _ _ h ↦ h⟩ :
    ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ).op) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.underNerveDiagram C

/-- 概要：底の射列の面・退化で undercategory の図式も同じ添字変換を受ける。
方針：有限順序の持ち上げと元へ戻す関手の合成を計算する。
規約：α は単射でも全射でもよい。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、評価の単体的自然性。 -/
lemma strictTransportSimplexUnderDiagram_reindex
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) :
    α.toOrderHom.uliftMap.toFunctor.op ⋙ strictTransportSimplexUnderDiagram σ =
      strictTransportSimplexUnderDiagram ((nerve C).map α.op σ) := rfl

/-- 概要：底の単体と fibration の coherent 単体を同じ添字で評価した 𝒮 の単体。
方針：射列上の undercategory の図式と coherent な fibration の図式に対角評価を使う。
規約：二つの入力の次数は同じ n。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手を curry する前の評価写像。 -/
noncomputable def strictTransportDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (nerve C)) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalRelativeEvaluation (strictTransportSimplexUnderDiagram σ) F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
