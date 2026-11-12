module
public import SerrePositivity.KST.SConstruction.ZeroRowPreviousComparison

/-! # 前の反復実現と既存の経路 fiber の共通 Kan 比較
概要：前段の既存の Kan 実現と次段の経路境界の既存の fiber へ、共通 Kan 模型から全基点 π_* 同型を作る。
方針：可縮零段の一頂点を選び、同じ点つき経路零行の Kan 模型の二つの厳密な延長を使う。
規約：この比較だけで元の suspension 構造射の Ω 条件とはしない。
使われ方：元の構造射と fiber 比較の照合における前段の同値模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open scoped Simplicial

/-- 前段の Kan 実現と既存の経路 fiber は共通 Kan 模型から全基点 π_* 同型で比較できる。 -/
lemma exists_previousStage_pathFiber_comparison (r : ℕ) (X : StableModel.{u}) :
    ∃ P : PointedKanComplex.{u},
      ∃ (a : P.space ⟶ (boundaryKanRealizationFunctor r).obj X)
        (b : P.space ⟶ iteratedPathHomotopyFiber (r + 1) X),
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism a.right ∧ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism b.right := by
  let b : ((iteratedSRealizationDiagram (r + 1) X).obj (Opposite.op ⦋0⦌)) _⦋0⦌ :=
    Classical.arbitrary _
  let P := PointedKanReplacement.obj (zeroRowPointedModel (r + 1) X b)
  exact ⟨⟨P, PointedKanReplacement.obj_kanComplex _⟩,
    zeroRowKanPreviousComparison r X b, zeroRowKanFiberComparison (r + 1) X b,
    zeroRowKanPreviousComparison_piIsomorphism r X b,
    zeroRowKanFiberComparison_piIsomorphism r X b⟩

end SerrePositivity.KST.SConstruction
