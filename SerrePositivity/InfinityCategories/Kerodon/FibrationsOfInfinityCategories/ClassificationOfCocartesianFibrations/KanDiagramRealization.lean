module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.DiagonalKanDiagramReindex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportJointEvaluation

/-!
概要：strict な Kan 値図式の coherent nerve を空間値関手として実現する。
方針：底の射列と図式の coherent 単体を対角評価し、共同評価を curry する。
規約：底の nerve を u+1 に持ち上げて coherent nerve と宇宙を揃える。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な Kan 値図式から関手 ∞ 圏への比較写像。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底の射列を coherent nerve の添字と同じ宇宙へ移す。
方針：有限順序の ULift から元へ戻す関手を前合成する。
規約：値は元の底 C の対象と射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な図式の対角評価の底の入力。 -/
def kanDiagramSimplexBase {C : Type u} [Category.{u} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : ULift.{u} (Fin (n + 1)) ⥤ C :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ :
    ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ

/-- 概要：strict な図式の coherent 単体を底の射列で対角評価する。
方針：持ち上げた射列と豊穣関手の対角評価を取る。
規約：二つの入力は同じ次数 n。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、図式の実現の共同評価の単体。 -/
noncomputable def kanDiagramDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ) F

/-- 概要：strict な図式の対角単体は面と退化に整合する。
方針：対角評価の添字変換則と有限順序の持ち上げの計算を使う。
規約：α は任意の単体圏の射。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共同評価の自然性。 -/
lemma kanDiagramDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.map α.op (kanDiagramDiagonalSimplex σ F) =
      kanDiagramDiagonalSimplex ((nerve C).map α.op σ)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C).map α.op F) := by
  change (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ) F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (kanDiagramSimplexBase ((nerve C).map α.op σ))
        ((SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet F)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation_reindex]
  rfl

/-- 概要：底と strict な Kan 値図式を同時に評価して 𝒮 へ写す。
方針：各次数の二つの単体を対角評価で結合する。
規約：左因子は持ち上げた底の nerve。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、図式の実現を curry する前の写像。 -/
noncomputable def kanDiagramJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app _ := ↾fun s ↦ kanDiagramDiagonalSimplex s.1.down s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (kanDiagramDiagonalSimplex_naturality α.unop s.1.down s.2).symm

/-- 概要：strict な Kan 値図式を coherent な空間値関手として実現する。
方針：底と図式の共同評価を curry する。
規約：ここではこの写像の同値性を主張しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、straightening と関手 ∞ 圏の比較の中間写像。 -/
noncomputable def kanDiagramRealization (C : Type u) [Category.{u} C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNerve C ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  curry (kanDiagramJointEvaluation C)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
