module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：左右の因子がともに現れる join の単体の両端の面による検出。
方針：最初の面は右因子を、最後の面は左因子をそのまま保つことを使う。
規約：補った単体の次数の等式は cast と HEq で明示する。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、区間付き対角に沿う内ホーンの充填。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：最初の頂点を除くと正の切断は一つ減る。
方針：各頂点が切断の左にある条件を比較する。
規約：切断 l は元の頂点数以下で正。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、join の最初の面の計算。 -/
lemma Join.pullCut_delta_zero (n l : ℕ) (hl : 0 < l) (hn : l ≤ n + 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom l = l - 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (n := n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (by omega)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff]
  change ((0 : Fin (n + 2)).succAbove i).val < l ↔ i.val < l - 1
  rw [Fin.succAbove_zero]
  change i.val + 1 < l ↔ i.val < l - 1
  omega

/-- 概要：最後の頂点を除いても、その手前の切断は変わらない。
方針：最後以外の頂点の値が変わらないことを使う。
規約：切断 l は取り除く最後の頂点より前。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、join の最後の面の計算。 -/
lemma Join.pullCut_delta_last (n l : ℕ) (hl : l ≤ n + 1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom l = l := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (n := n + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) hl
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff]
  change ((Fin.last (n + 1)).succAbove i).val < l ↔ i.val < l
  rw [Fin.succAbove_last]
  rfl

/-- 概要：正の切断を持つ join の最初の面は右の単体を保つ。
方針：右区間の頂点数と制限の順序写像が恒等写像と一致することを示す。
規約：頂点数が命題的に一致するため HEq で述べる。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、混合単体の右因子の復元。 -/
lemma Join.simplexMap_delta_zero_right_heq {X Y : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1)) (hs : 0 < s.1.val) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom s).2.2 s.2.2 := by
  let α := (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val = s.1.val - 1 :=
    Join.pullCut_delta_zero n s.1.val hs (by have := s.1.isLt; omega)
  have hm : n + 1 - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val = n + 2 - s.1.val := by
    rw [hc]
    have := s.1.isLt
    omega
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_congr Y hm rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) OrderHom.id
    (fun i j hij ↦ by
      change ((0 : Fin (n + 2)).succAbove ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + i.val, by have := i.isLt; omega⟩).val - s.1.val = j.val
      rw [Fin.succAbove_zero]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + i.val + 1 - s.1.val = j.val
      omega) s.2.2 s.2.2 rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_id] at he
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) s.2.2) s.2.2
  exact (cast_heq _ _).symm.trans (heq_of_eq he)

/-- 概要：最後より手前に切断を持つ join の最後の面は左の単体を保つ。
方針：左区間の制限が恒等写像であることを等式に沿って移送する。
規約：頂点数の輸送を HEq で明示する。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、混合単体の左因子の復元。 -/
lemma Join.simplexMap_delta_last_left_heq {X Y : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1)) (hs : s.1.val ≤ n + 1) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s).2.1 s.2.1 := by
  let α := (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val = s.1.val := Join.pullCut_delta_last n s.1.val hs
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_congr X hc rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α s.1.val) OrderHom.id
    (fun i j hij ↦ by
      change ((Fin.last (n + 1)).succAbove ⟨i.val, _⟩).val = j.val
      rw [Fin.succAbove_last]
      exact hij) s.2.1 s.2.1 rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_id] at he
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α s.1.val) s.2.1) s.2.1
  exact (cast_heq _ _).symm.trans (heq_of_eq he)

/-- 概要：左右の因子がともに現れる join の二つの単体は切断と最初・最後の面で一致を判定できる。
方針：最後の面から左因子、最初の面から右因子を復元し、依存和の外延性を使う。
規約：二つの単体の次数と切断は等しい。
使われ方：Kerodon Lemma 5.2.3.12（Tag 024D）、内ホーンの充填後の比較。 -/
lemma Join.Simplex.ext_of_extreme_faces {X Y : SSet.{u}} {n : ℕ}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1)) (hc : s.1 = t.1)
    (hs0 : 0 < s.1.val) (hs1 : s.1.val ≤ n + 1)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom t)
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t) : s = t := by
  have ht0 : 0 < t.1.val := by rw [← hc]; exact hs0
  have ht1 : t.1.val ≤ n + 1 := by rw [← hc]; exact hs1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext s t hc
  · have hh : HEq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom s).2.1
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t).2.1 := by rw [h1]
    have he := (Join.simplexMap_delta_last_left_heq s hs1).symm.trans
      (hh.trans (Join.simplexMap_delta_last_left_heq t ht1))
    exact eq_of_heq ((cast_heq _ _).trans he)
  · have hh : HEq
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom s).2.2
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom t).2.2 := by rw [h0]
    have he := (Join.simplexMap_delta_zero_right_heq s hs0).symm.trans
      (hh.trans (Join.simplexMap_delta_zero_right_heq t ht0))
    exact eq_of_heq ((cast_heq _ _).trans he)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.Simplex (ext_of_extreme_faces)


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
