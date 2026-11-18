module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutValidity
public import Mathlib.Data.List.Nodup

/-!
模型。文献の定義との比較は後で
# 辺切断の非退化性と左右リストの重複消滅

概要：Berger–Fresse §2.2.1 の非零な辺切断を、切断点を共有する二つのリストの Nodup で表す。
方針：正規化の左右単射性を take・drop の有限位置で評価する。
規約：切断点は左右の両リストに一回ずつ含む。
使われ方：挿入語を連結した切断の非退化性とその逆の復元。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：非零切断の左の接頭語には重複がない（BF §2.2.1）。
方針：有限リストの位置の単射性を元の語の左単射性で示す。
規約：接頭語は切断点の文字を含む。
使われ方：一出現挿入の前半の Nodup 条件。 -/
lemma cut_prefix_nodup {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : ((List.ofFn u).take (p.val + 1)).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  simp only [List.length_take, List.length_ofFn] at hi hj
  have hli : i.val < l := by omega
  have hlj : j.val < l := by omega
  have hv : u ⟨i.val, hli⟩ = u ⟨j.val, hlj⟩ := by
    simpa only [List.getElem_take, List.getElem_ofFn] using he
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h ⟨i.val, hli⟩ ⟨j.val, hlj⟩
    (by change i.val ≤ p.val; omega) (by change j.val ≤ p.val; omega) hv
  have hpos := congrArg Fin.val hp
  exact Fin.ext hpos

/-- 概要：非零切断の右の接尾語には重複がない（BF §2.2.1）。
方針：drop 後の位置を切断点の値だけずらし、右単射性を使う。
規約：接尾語は切断点の文字から始まる。
使われ方：一出現挿入の後半の Nodup 条件。 -/
lemma cut_suffix_nodup {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : ((List.ofFn u).drop p.val).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j he
  have hi := i.isLt
  have hj := j.isLt
  simp only [List.length_drop, List.length_ofFn] at hi hj
  have hli : p.val + i.val < l := by omega
  have hlj : p.val + j.val < l := by omega
  have hv : u ⟨p.val + i.val, hli⟩ = u ⟨p.val + j.val, hlj⟩ := by
    simpa only [List.getElem_drop, List.getElem_ofFn] using he
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h ⟨p.val + i.val, hli⟩ ⟨p.val + j.val, hlj⟩
    (by change p.val ≤ p.val + i.val; omega) (by change p.val ≤ p.val + j.val; omega) hv
  have hvp := congrArg Fin.val hp
  apply Fin.ext
  change p.val + i.val = p.val + j.val at hvp
  omega

/-- 概要：切断点を共有する左右の語に重複がなければ辺切断は非退化（BF §2.2.1）。
方針：左右の単射性を、take・drop の位置の単射性から元位置へ戻す。
規約：元の語の全射性・隣接非退化性は要求しない。
使われ方：部分合成で連結した非零切断の構成。 -/
lemma cut_nondegenerate_of_nodup {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (hL : ((List.ofFn u).take (p.val + 1)).Nodup)
    (hR : ((List.ofFn u).drop p.val).Nodup) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
  constructor
  · intro i j hi hj he
    let i' : Fin (((List.ofFn u).take (p.val + 1)).length) :=
      ⟨i.val, by simp only [List.length_take, List.length_ofFn]; omega⟩
    let j' : Fin (((List.ofFn u).take (p.val + 1)).length) :=
      ⟨j.val, by simp only [List.length_take, List.length_ofFn]; omega⟩
    have hv : ((List.ofFn u).take (p.val + 1))[i'.val] =
        ((List.ofFn u).take (p.val + 1))[j'.val] := by
      simpa only [List.getElem_take, List.getElem_ofFn] using he
    have hpos := congrArg Fin.val (List.nodup_iff_injective_getElem.mp hL hv)
    exact Fin.ext hpos
  · intro i j hi hj he
    let i' : Fin (((List.ofFn u).drop p.val).length) :=
      ⟨i.val - p.val, by simp only [List.length_drop, List.length_ofFn]; omega⟩
    let j' : Fin (((List.ofFn u).drop p.val).length) :=
      ⟨j.val - p.val, by simp only [List.length_drop, List.length_ofFn]; omega⟩
    have hpi : p.val + (i.val - p.val) = i.val := by omega
    have hpj : p.val + (j.val - p.val) = j.val := by omega
    have hv : ((List.ofFn u).drop p.val)[i'.val] = ((List.ofFn u).drop p.val)[j'.val] := by
      simpa only [i', j', List.getElem_drop, List.getElem_ofFn, hpi, hpj] using he
    have hpos := congrArg Fin.val (List.nodup_iff_injective_getElem.mp hR hv)
    apply Fin.ext
    change i.val - p.val = j.val - p.val at hpos
    omega

/-- 概要：辺切断の非退化性は左右のリストの重複消滅と同値（BF §2.2.1）。
方針：有限語の左右単射性とリストの位置単射性を両方向に比較する。
規約：左右とも切断点を含む。
使われ方：合成切断の順逆構成をリストの連結で証明する。 -/
lemma edgeNondegenerate_iff_list_nodup {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p ↔ ((List.ofFn u).take (p.val + 1)).Nodup ∧
      ((List.ofFn u).drop p.val).Nodup :=
  ⟨fun h => ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup u p h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup u p h⟩,
    fun h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup u p h.1 h.2⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
