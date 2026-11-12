module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinStdSimplexVertices

/-!
概要：最後の頂点を取らない標準単体間の射の最後の面への因子化。
方針：頂点の順序写像の全ての値が最後の値以下であることから終域を一つ小さくする。
規約：終域は標準 n+1 単体、因子化先は標準 n 単体。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、f(m)<n の場合の終域の次元の帰納。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：終域の最後の頂点を除いた有限鎖への因子化の順序写像。
方針：元の射の最後の値より全ての値が小さいことを使って Fin の上界を変更する。
規約：値の自然数としての番号は変えない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、最後の面への因子化の構成。 -/
noncomputable def stdSimplexLastFaceOrderHom {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) < Fin.last (n + 1)) :
    Fin (m + 1) →o Fin (n + 1) where
  toFun i := ⟨((SSet.yonedaEquiv f) i).val, by
    have hi := stdSimplex.monotone_apply (SSet.yonedaEquiv f) (Fin.le_last i)
    change ((SSet.yonedaEquiv f) i).val ≤ ((SSet.yonedaEquiv f) (Fin.last m)).val at hi
    change ((SSet.yonedaEquiv f) (Fin.last m)).val < n + 1 at hf
    omega⟩
  monotone' i j h := stdSimplex.monotone_apply (SSet.yonedaEquiv f) h

/-- 概要：最後の頂点を取らない標準単体間の射を最後の面へ因子化する射。
方針：終域を小さくした順序写像に標準単体関手を適用する。
規約：順方向の最後の面の包含との合成で元の射に戻る。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域の次元を一つ下げる入力。 -/
noncomputable def stdSimplexLastFaceFactor {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) < Fin.last (n + 1)) :
    (Δ[m] : SSet.{u}) ⟶ Δ[n] :=
  stdSimplex.map (SimplexCategory.mkHom (stdSimplexLastFaceOrderHom f hf))

/-- 概要：小さい標準単体への因子化に最後の面の包含を合成すると元の射になる。
方針：Yoneda の対応で全頂点の自然数としての値を比較する。
規約：最後の面の包含は δ の最後の添字。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、次元を下げた比較から元の比較への移送。 -/
lemma stdSimplexLastFaceFactor_comp {m n : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Δ[n + 1])
    (hf : (SSet.yonedaEquiv f) (Fin.last m) < Fin.last (n + 1)) :
    stdSimplexLastFaceFactor f hf ≫ stdSimplex.δ (Fin.last (n + 1)) = f := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change ((Fin.last (n + 1)).succAbove (stdSimplexLastFaceOrderHom f hf i)).val =
    ((SSet.yonedaEquiv f) i).val
  rw [Fin.succAbove_last]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
