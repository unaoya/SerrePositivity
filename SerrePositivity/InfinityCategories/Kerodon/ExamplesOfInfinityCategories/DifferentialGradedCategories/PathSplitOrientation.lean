module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathSplitCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeSumFlags
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DescendingDeletion

/-!
# Path の左右分解と降順の向き

概要：後半の降順番号付けと前半の降順番号付けを連結すると、切断点を除いた全体の降順になる。
方針：各区間内の順序と、後半の点が全て前半の点より大きいことを使う。
規約：後半を先に並べることで AW の因子の順と降順の向きを一致させる。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の合成面の基本鎖の向きの照合。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：後半と前半の番号付けを連結し、切断点を除いた座標を番号付けする。
方針：和の番号付けを座標の左右分解の逆で元の有限集合へ戻す。
規約：先頭区間が後半、末尾区間が前半。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面の全座標の番号付け。 -/
def pathSplitEnumeration (S : Finset (Set.Ioo a b)) (j : S) {p q : ℕ}
    (e : Fin p ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (f : Fin q ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) : Fin (p + q) ≃ ↥(S.erase j.val) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm

/-- 概要：連結した番号付けの先頭の点の値は元の後半の点の値である。
方針：和の左側と左右分解の逆で値を計算する。
規約：元の順序集合での値の等式。
使われ方：HA 1.3.1.16 の後半の番号の向きの確認。 -/
lemma pathSplitEnumeration_castAdd_val (S : Finset (Set.Ioo a b)) (j : S) {p q : ℕ}
    (e : Fin p ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (f : Fin q ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) (r : Fin p) :
    (pathSplitEnumeration S j e f (Fin.castAdd q r)).val.val = (e r).val.val := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f (Fin.castAdd q r))).val.val = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inl_val S j (e r)

/-- 概要：連結した番号付けの末尾の点の値は元の前半の点の値である。
方針：和の右側と左右分解の逆で値を計算する。
規約：元の順序集合での値の等式。
使われ方：HA 1.3.1.16 の前半の番号の向きの確認。 -/
lemma pathSplitEnumeration_natAdd_val (S : Finset (Set.Ioo a b)) (j : S) {p q : ℕ}
    (e : Fin p ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (f : Fin q ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) (r : Fin q) :
    (pathSplitEnumeration S j e f (Fin.natAdd p r)).val.val = (f r).val.val := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv S j).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f (Fin.natAdd p r))).val.val = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathSplitCoordinateEquiv_symm_inr_val S j (f r)

/-- 概要：後半と前半が降順なら、連結した全体の番号付けも降順である。
方針：二つの区間内と区間をまたぐ四つの場合に分ける。
規約：後半の任意の点は切断点より大きく、前半の任意の点は小さい。
使われ方：Kerodon 2.5.9（Tag 00SC） の基本鎖の向きに新しい置換符号が生じないこと。 -/
lemma pathSplitEnumeration_strictAnti (S : Finset (Set.Ioo a b)) (j : S) {p q : ℕ}
    (e : Fin p ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (f : Fin q ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) (he : StrictAnti e) (hf : StrictAnti f) :
    StrictAnti (pathSplitEnumeration S j e f) := by
  intro r s hrs
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective r
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective s
  cases r with
  | inl r =>
    cases s with
    | inl s =>
      change (pathSplitEnumeration S j e f (Fin.castAdd q s)).val.val <
        (pathSplitEnumeration S j e f (Fin.castAdd q r)).val.val
      rw [pathSplitEnumeration_castAdd_val, pathSplitEnumeration_castAdd_val]
      exact he hrs
    | inr s =>
      change (pathSplitEnumeration S j e f (Fin.natAdd p s)).val.val <
        (pathSplitEnumeration S j e f (Fin.castAdd q r)).val.val
      rw [pathSplitEnumeration_natAdd_val, pathSplitEnumeration_castAdd_val]
      exact lt_trans (f s).val.property.2 (e r).val.property.1
  | inr r =>
    cases s with
    | inl s =>
      have h : p + r.val < s.val := hrs
      have hs := s.isLt
      omega
    | inr s =>
      change (pathSplitEnumeration S j e f (Fin.natAdd p s)).val.val <
        (pathSplitEnumeration S j e f (Fin.natAdd p r)).val.val
      rw [pathSplitEnumeration_natAdd_val, pathSplitEnumeration_natAdd_val]
      apply hf
      change r.val < s.val
      have h : p + r.val < p + s.val := hrs
      omega

/-- 概要：左右の降順番号付けの連結は切断点を除いた集合の標準降順番号付けに等しい。
方針：連結が降順であることと降順番号付けの一意性を使う。
規約：濃度の等式を引数に取り、Fin の次数の移送を避ける。
使われ方：HA 1.3.1.16 の合成面と全体の削除面の基本鎖の向きの同定。 -/
lemma pathSplitEnumeration_eq_descending (S : Finset (Set.Ioo a b)) (j : S) {p q : ℕ}
    (e : Fin p ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b))
    (f : Fin q ≃ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val)) (he : StrictAnti e) (hf : StrictAnti f)
    (h : (S.erase j.val).card = p + q) :
    pathSplitEnumeration S j e f = Fin.revPerm.trans ((S.erase j.val).orderIsoOfFin h).toEquiv := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.strictAnti_enumeration_unique
  · exact pathSplitEnumeration_strictAnti S j e f he hf
  · exact ((S.erase j.val).orderIsoOfFin h).strictMono.comp_strictAnti Fin.rev_strictAnti

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
