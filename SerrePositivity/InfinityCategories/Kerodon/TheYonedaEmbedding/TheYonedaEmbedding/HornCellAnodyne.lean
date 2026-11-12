module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.HornCellStep
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory

/-!
概要：全ホーンの一段のセル付加の単位は anodyne である。
方針：各ホーンのコピーと全ホーンの余積で anodyne 性を保ち、pushout に沿って移す。
規約：具体的な関手の元の単位射について証明する。
使われ方：可算反復の単位の anodyne 性と弱同値性。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：anodyne なセルの射を全コピーで繰り返しても anodyne。
方針：同じ射の余積に対する anodyne 性の閉性を使う。
規約：添字に用いる始域 A の有限性は不要。使われ方：各ホーンの全コピーの境界。 -/
lemma cellCopiesMap_anodyne (A : SSet.{u}) {B D : SSet.{u}} (i : B ⟶ D)
    (hi : anodyneExtensions i) (X : SSet.{u}) :
    anodyneExtensions ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesMap A i).app X) := by
  change anodyneExtensions (colimMap (Discrete.natTrans
    (F := Discrete.functor (fun _ : A ⟶ X ↦ B))
    (G := Discrete.functor (fun _ : A ⟶ X ↦ D)) (fun _ ↦ i)))
  exact anodyneExtensions.colimMap _ (fun _ ↦ hi)

/-- 概要：全ホーンのコピーの境界射は各対象で anodyne。
方針：ホーン包含のコピーの anodyne 性を関手圏の余積で保つ。
規約：全ての次元と全てのホーンを含む。使われ方：一段のセル付加の左辺。 -/
lemma hornCopiesBoundary_anodyne (X : SSet.{u}) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.app X) := by
  have h : (anodyneExtensions.{u}.functorCategory SSet.{u}) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u} := by
    change (anodyneExtensions.{u}.functorCategory SSet.{u})
      (colimMap (Discrete.natTrans
        (F := Discrete.functor (fun h : Σ n : ℕ, Fin (n + 2) ↦
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) (horn (h.1 + 1) h.2)))
        (G := Discrete.functor (fun h : Σ n : ℕ, Fin (n + 2) ↦
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) Δ[h.1 + 1]))
        (fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesMap.{u} (horn (h.as.1 + 1) h.as.2)
          (horn (h.as.1 + 1) h.as.2).ι)))
    apply MorphismProperty.colimMap
    intro h X
    exact cellCopiesMap_anodyne _ _ (anodyneExtensions.horn_ι h.as.2) X
  exact h X

/-- 概要：全ホーンを一段付加する元の単位射は anodyne。
方針：関手圏の pushout を X で評価し、境界射の anodyne 性を押し出す。
規約：X 自体の Kan 性は不要。使われ方：反復の各後続射の弱同値性。 -/
lemma hornCellStepUnit_anodyne (X : SSet.{u}) :
    anodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCellStepUnit.app X) := by
  have h := (IsPushout.of_hasPushout _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesEvaluation.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.hornCopiesBoundary.{u}).map
    ((evaluation SSet.{u} SSet.{u}).obj X)
  exact anodyneExtensions.of_isPushout h (hornCopiesBoundary_anodyne X)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
