module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.FiniteCellCopies
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：全てのホーンを同時に付加するための関手の図式。
方針：各ホーンへの全ての射を添字に持つセル余積を、全次元・全頂点で余積する。
規約：始域の余積を元の対象へ評価し、終域の余積への射と pushout を取る準備をする。
使われ方：filtered 余極限を保つ具体的な Kan 置換のセル付加。

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

/-- 概要：全てのホーンの始域のコピーの余積。
方針：各次元と除外頂点でホーン自身のコピー関手を並べる。
規約：添字は n 次元ではなく n+1 次元のホーン。使われ方：セル付加の始域。 -/
def hornSourceCopies : SSet.{u} ⥤ SSet.{u} :=
  ∐ fun h : Σ n : ℕ, Fin (n + 2) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) (horn (h.1 + 1) h.2)

/-- 概要：全てのホーンの終域のコピーの余積。
方針：各ホーンからの射で対応する標準単体を添字付ける。
規約：添字の射は終域ではなくホーンからの射。使われ方：付加するセル全体。 -/
def hornTargetCopies : SSet.{u} ⥤ SSet.{u} :=
  ∐ fun h : Σ n : ℕ, Fin (n + 2) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesFunctor (horn (h.1 + 1) h.2 : SSet.{u}) Δ[h.1 + 1]

/-- 概要：ホーンのコピーを添字の射で元の対象へ評価する。
方針：各コピー関手の評価を余積からの射に束ねる。
規約：全ての次元と除外頂点を保持する。使われ方：付加の pushout の上辺。 -/
def hornCopiesEvaluation : hornSourceCopies.{u} ⟶ 𝟭 SSet.{u} :=
  Sigma.desc fun h ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesEvaluation (horn (h.1 + 1) h.2)

/-- 概要：ホーンの包含は始域のコピーの余積から終域のコピーの余積への射を与える。
方針：同じ添字を保つコピーの射を余積する。
規約：各セルの境界射は元のホーン包含。使われ方：付加の pushout の左辺。 -/
def hornCopiesBoundary : hornSourceCopies.{u} ⟶ hornTargetCopies.{u} :=
  Limits.Sigma.map fun h : Σ n : ℕ, Fin (n + 2) ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.cellCopiesMap (horn (h.1 + 1) h.2) (horn (h.1 + 1) h.2).ι

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
