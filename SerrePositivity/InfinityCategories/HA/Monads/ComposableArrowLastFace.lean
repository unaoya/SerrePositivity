module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces

/-!
概要：最後の実面は、最後の頂点より前の実対象と実射をそのまま回収する。
方針：最後の点を除く有限順序埋め込みをcastSuccの実関手へ同一視する。
規約：全対象・全隣接実辺を元の全鎖と比較する。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実最終面の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：最後の点を飛ばす実順序関手はcastSuccの関手。
方針：全頂点のsuccAboveと薄い圏の射を比較する。
規約：全実関手の等式。使われ方：Riehl–Verity Lemma 4.1.4の実最後の面。 -/
lemma finiteChainFaceIndex_last (n : ℕ) :
    finiteChainFaceIndex (Fin.last (n + 1)) = Fin.castSuccFunctor (n + 1) := by
  refine CategoryTheory.Functor.ext (fun i => Fin.succAbove_last_apply i) ?_
  intro a b f
  exact Subsingleton.elim _ _

/-- 概要：最後の実面の対象は最後より前の元の対象。
方針：実添字関手の等式を各有限点で評価する。
規約：実対象の等式。使われ方：Riehl–Verity Lemma 4.1.4の実端点の回収。 -/
lemma finiteChainFace_last_obj {n : ℕ} (F : ComposableArrows C (n + 1)) (i : Fin (n + 1)) :
    (finiteChainFace F (Fin.last (n + 1))).obj i = F.obj i.castSucc := by
  rw [finiteChainFace, finiteChainFaceIndex_last]
  rfl

/-- 概要：最後の実面の全隣接辺は最後より前の元の実辺。
方針：実添字関手の等式を元の実射で評価する。
規約：対象の輸送の前は異種等式。使われ方：Riehl–Verity Lemma 4.1.4の実辺の回収。 -/
lemma finiteChainFace_last_edge {n : ℕ} (F : ComposableArrows C (n + 2)) (j : Fin (n + 1)) :
    HEq ((finiteChainFace F (Fin.last (n + 2))).map
      (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.castSucc))) := by
  rw [finiteChainFace, finiteChainFaceIndex_last]
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
