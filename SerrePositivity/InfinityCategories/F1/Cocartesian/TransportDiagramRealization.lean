module

public import SerrePositivity.InfinityCategories.F1.Diagrams.DiagonalCocartesianTransportDiagramReindex
public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramRealization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.StraighteningCoherent

/-!
概要：strict transport 図式の中間 ∞ 圏を Cat∞ 値関手として実現する。
方針：底の射列と図式の coherent 単体を元の core の作用で対角評価し、共同評価を curry する。
規約：元の図式の全高次を実現し、底とパラメーターの宇宙を揃える。
使われ方：元の Cat∞ 値 straightening 主写像の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：strict な図式の coherent 単体を底の射列で対角評価する。
方針：持ち上げた射列と豊穣関手の対角評価を取る。
規約：二つの入力は同じ次数 n。
使われ方：Kerodon Corollary 5.6.0.6、像の実現の共同評価の単体。 -/
noncomputable def cocartesianTransportDiagramDiagonalSimplex
    {C : Type u} [Category.{u} C] {n : ℕ} (σ : (nerve C) _⦋n⦌)
    (F : (CocartesianTransportDiagramInfinity C) _⦋n⦌) : CatInfinity.{u} _⦋n⦌ :=
  diagonalCocartesianTransportDiagramEvaluation (strictDiagramSimplexBase σ) F

/-- 概要：strict な図式の対角単体は面と退化に整合する。
方針：対角評価の添字変換則と有限順序の持ち上げの計算を使う。
規約：α は任意の単体圏の射。
使われ方：Kerodon Corollary 5.6.0.6、共同評価の自然性。 -/
lemma cocartesianTransportDiagramDiagonalSimplex_naturality
    {C : Type u} [Category.{u} C] {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (nerve C) _⦋n⦌) (F : (CocartesianTransportDiagramInfinity C) _⦋n⦌) :
    CatInfinity.map α.op (cocartesianTransportDiagramDiagonalSimplex σ F) =
      cocartesianTransportDiagramDiagonalSimplex ((nerve C).map α.op σ)
        ((CocartesianTransportDiagramInfinity C).map α.op F) := by
  change (SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet
    (diagonalCocartesianTransportDiagramEvaluation (strictDiagramSimplexBase σ) F) =
      diagonalCocartesianTransportDiagramEvaluation (strictDiagramSimplexBase ((nerve C).map α.op
        σ))
        ((SimplicialThickening.functor α.toOrderHom.uliftMap).comp SSet F)
  rw [diagonalCocartesianTransportDiagramEvaluation_reindex]
  rfl

/-- 概要：底と strict transport の像を同時に評価して Cat∞ へ写す。
方針：各次数の二つの単体を対角評価で結合する。
規約：左因子は持ち上げた底の nerve。
使われ方：Kerodon Corollary 5.6.0.6、像の実現を curry する前の写像。 -/
noncomputable def cocartesianTransportDiagramJointEvaluation (C : Type u) [Category.{u} C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⊗ CocartesianTransportDiagramInfinity C ⟶
      CatInfinity.{u} where
  app _ := ↾fun s ↦ cocartesianTransportDiagramDiagonalSimplex s.1.down s.2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (cocartesianTransportDiagramDiagonalSimplex_naturality α.unop s.1.down s.2).symm

/-- 概要：strict transport の像を coherent な空間値関手として実現する。
方針：底と像の共同評価を curry する。
規約：ここではこの写像の同値性を主張しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening と関手 ∞ 圏の比較の中間写像。 -/
noncomputable def cocartesianTransportDiagramRealization (C : Type u) [Category.{u} C] :
    CocartesianTransportDiagramInfinity C ⟶
      CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) :=
  curry (cocartesianTransportDiagramJointEvaluation C)

end SerrePositivity.InfinityCategories
