module

public import SerrePositivity.InfinityCategories.F1.DiagonalStrictDiagramReindex
public import SerrePositivity.InfinityCategories.F1.StrictTransportJointEvaluation

/-!
概要：strict transport の像の coherent nerve を空間値関手として実現する。
方針：底の射列と図式の coherent 単体を対角評価し、共同評価を curry する。
規約：底の nerve を u+1 に持ち上げて coherent nerve と宇宙を揃える。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の像から関手 ∞ 圏への比較写像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の射列を coherent nerve の添字と同じ宇宙へ移す。
方針：有限順序の ULift から元へ戻す関手を前合成する。
規約：値は元の底 C の対象と射。
使われ方：Kerodon Corollary 5.6.0.6、strict な図式の対角評価の底の入力。 -/
def strictDiagramSimplexBase {C : Type u} [Category.{u} C] {n : ℕ}
    (σ : (nerve C) _⦋n⦌) : ULift.{u} (Fin (n + 1)) ⥤ C :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ :
    ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙ σ

/-- 概要：strict な図式の coherent 単体を底の射列で対角評価する。
方針：持ち上げた射列と豊穣関手の対角評価を取る。
規約：二つの入力は同じ次数 n。
使われ方：Kerodon Corollary 5.6.0.6、像の実現の共同評価の単体。 -/
noncomputable def strictDiagramDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (StrictTransportDiagramInfinity C) _⦋n⦌) : SpaceInfinity.{u} _⦋n⦌ :=
  diagonalStrictDiagramEvaluation (strictDiagramSimplexBase σ) F

/-- 概要：strict な図式の対角単体は面と退化に整合する。
方針：対角評価の添字変換則と有限順序の持ち上げの計算を使う。
規約：α は任意の単体圏の射。
使われ方：Kerodon Corollary 5.6.0.6、共同評価の自然性。 -/
lemma strictDiagramDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (StrictTransportDiagramInfinity C) _⦋n⦌) :
    SpaceInfinity.map α.op (strictDiagramDiagonalSimplex σ F) =
      strictDiagramDiagonalSimplex ((nerve C).map α.op σ)
        ((StrictTransportDiagramInfinity C).map α.op F) := by
  change (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
    (diagonalStrictDiagramEvaluation (strictDiagramSimplexBase σ) F) =
      diagonalStrictDiagramEvaluation (strictDiagramSimplexBase ((nerve C).map α.op σ))
        ((SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet F)
  rw [diagonalStrictDiagramEvaluation_reindex]
  rfl

/-- 概要：底と strict transport の像を同時に評価して 𝒮 へ写す。
方針：各次数の二つの単体を対角評価で結合する。
規約：左因子は持ち上げた底の nerve。
使われ方：Kerodon Corollary 5.6.0.6、像の実現を curry する前の写像。 -/
noncomputable def strictDiagramJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ StrictTransportDiagramInfinity C ⟶
      SpaceInfinity.{u} where
  app _ := ↾fun s ↦ strictDiagramDiagonalSimplex s.1.down s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (strictDiagramDiagonalSimplex_naturality α.unop s.1.down s.2).symm

/-- 概要：strict transport の像を coherent な空間値関手として実現する。
方針：底と像の共同評価を curry する。
規約：ここではこの写像の同値性を主張しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening と関手 ∞ 圏の比較の中間写像。 -/
noncomputable def strictTransportDiagramRealization (C : Type u) [Category.{u} C] :
    StrictTransportDiagramInfinity C ⟶
      SpaceInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  curry (strictDiagramJointEvaluation C)

end SerrePositivity.InfinityCategories
