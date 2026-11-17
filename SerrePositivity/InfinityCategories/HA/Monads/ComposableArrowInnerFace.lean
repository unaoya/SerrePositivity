module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces

/-!
概要：内側の実面の全対象と辺を、元の鎖と指定した二辺の合成から回収する。
方針：一点を除く有限順序関手の前後の値と全合成を照合する。
規約：辺は対象の等式の前は異種等式で保持する。
使われ方：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の内側の実面の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：面の二頂点の実添字が一致すれば、その間の実射も一致する。
方針：二つの実添字を同一視して薄い有限順序圏の射へ戻す。
規約：対象の輸送の前は異種等式。使われ方：Riehl–Verity Lemma 4.1.3の実面。 -/
lemma finiteChainFace_map_heq_of_indices {n : ℕ} (F : ComposableArrows C (n + 1))
    (p : Fin (n + 2)) {a b : Fin (n + 1)} {a' b' : Fin (n + 2)}
    (ha : p.succAbove a = a') (hb : p.succAbove b = b') (hab : a ≤ b) (hab' : a' ≤ b') :
    HEq ((finiteChainFace F p).map (homOfLE hab)) (F.map (homOfLE hab')) := by
  subst a'
  subst b'
  rfl

/-- 概要：内側の面の挿入位置までの実対象は元の同じ位置。
方針：飛ばす点より左の実有限添字を計算する。規約：実対象の等式。
使われ方：Riehl–Verity Lemma 4.1.3の元の実始点の回収。 -/
lemma finiteChainFace_inner_before_obj {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) (i : Fin (n + 2)) (hi : i.val ≤ k.val) :
    (finiteChainFace F k.succ.castSucc).obj i = F.obj i.castSucc := by
  change F.obj (k.succ.castSucc.succAbove i) = F.obj i.castSucc
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < k.val + 1; omega)]

/-- 概要：内側の面の挿入位置より後の実対象は元の一つ後の位置。
方針：飛ばす点より右の実有限添字を計算する。規約：実対象の等式。
使われ方：Riehl–Verity Lemma 4.1.3の実終点の回収。 -/
lemma finiteChainFace_inner_after_obj {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) (i : Fin (n + 2)) (hi : k.val < i.val) :
    (finiteChainFace F k.succ.castSucc).obj i = F.obj i.succ := by
  change F.obj (k.succ.castSucc.succAbove i) = F.obj i.succ
  rw [Fin.succAbove_of_le_castSucc _ _ (by change k.val + 1 ≤ i.val; omega)]

/-- 概要：内側の面の指定位置より前の実辺は元の同じ実辺。
方針：両実頂点を飛ばす点より左へ戻す。規約：全先行実辺の異種等式。
使われ方：Riehl–Verity Lemma 4.1.3の最初の実併合位置の保存。 -/
lemma finiteChainFace_inner_before_edge {n : ℕ} (F : ComposableArrows C (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) :
    HEq ((finiteChainFace F k.succ.castSucc).map (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.castSucc))) := by
  apply finiteChainFace_map_heq_of_indices F k.succ.castSucc
  · apply Fin.succAbove_of_castSucc_lt
    change j.val < k.val + 1
    change j.val < k.val at hj
    omega
  · apply Fin.succAbove_of_castSucc_lt
    change j.val + 1 < k.val + 1
    change j.val < k.val at hj
    omega

/-- 概要：内側の面の指定位置より後の実辺は元の一つ後の実辺。
方針：両実頂点を飛ばす点より右へ戻す。規約：全後続実辺の異種等式。
使われ方：Riehl–Verity Lemma 4.1.3の非退化性の回収。 -/
lemma finiteChainFace_inner_after_edge {n : ℕ} (F : ComposableArrows C (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) :
    HEq ((finiteChainFace F k.succ.castSucc).map (homOfLE (Fin.castSucc_le_succ j)))
      (F.map (homOfLE (Fin.castSucc_le_succ j.succ))) := by
  apply finiteChainFace_map_heq_of_indices F k.succ.castSucc
  · apply Fin.succAbove_of_le_castSucc
    change k.val + 1 ≤ j.val
    change k.val < j.val at hj
    omega
  · apply Fin.succAbove_of_le_castSucc
    change k.val + 1 ≤ j.val + 1
    change k.val < j.val at hj
    omega

/-- 概要：内側の面の指定辺は元の実二辺の合成。
方針：両実頂点の添字と元の関手の合成則を使う。
規約：元の実二辺を保持する異種等式。使われ方：Riehl–Verity Lemma 4.1.3の実併合。 -/
lemma finiteChainFace_inner_merged_edge {n : ℕ} (F : ComposableArrows C (n + 2))
    (k : Fin (n + 1)) :
    HEq ((finiteChainFace F k.succ.castSucc).map (homOfLE (Fin.castSucc_le_succ k)))
      (F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
        F.map (homOfLE (Fin.castSucc_le_succ k.succ))) := by
  have ha : k.succ.castSucc.succAbove k.castSucc = k.castSucc.castSucc :=
    Fin.succAbove_of_castSucc_lt _ _ (by change k.val < k.val + 1; omega)
  have hb : k.succ.castSucc.succAbove k.succ = k.succ.succ := Fin.succAbove_castSucc_self _
  have hac : k.castSucc.castSucc ≤ k.succ.succ := by change k.val ≤ k.val + 2; omega
  have hm := finiteChainFace_map_heq_of_indices F k.succ.castSucc ha hb
    (Fin.castSucc_le_succ k) hac
  have he : F.map (homOfLE hac) = F.map (homOfLE (Fin.castSucc_le_succ k.castSucc)) ≫
      F.map (homOfLE (Fin.castSucc_le_succ k.succ)) := by
    rw [← F.map_comp]
    rfl
  exact hm.trans (heq_of_eq he)

/-- 概要：内側の実面は元の実終点を保つ。
方針：飛ばす点より後の最後の実対象を評価する。規約：実対象の等式。
使われ方：Riehl–Verity Lemma 4.1.3の原子性の回収。 -/
lemma finiteChainFace_inner_last {n : ℕ} (F : ComposableArrows C (n + 2)) (k : Fin (n + 1)) :
    (finiteChainFace F k.succ.castSucc).obj (Fin.last (n + 1)) = F.obj (Fin.last (n + 2)) := by
  exact finiteChainFace_inner_after_obj F k _ (by have hk := k.isLt; change k.val < n + 1; omega)

end SerrePositivity.InfinityCategories.HA.Monads
