module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathIntervalCoordinates

/-!
# 切断点を除いた Path の座標の左右分解

概要：切断点を除いた有限座標集合を、後半と前半の開区間の有限座標集合の和に分ける。
方針：切断点との大小で場合分けし、区間の座標の順序同型を使う。
規約：降順の向きと AW の順に合わせて後半の座標を和の左側に置く。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の合成面の座標の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：切断点を除いた座標は後半と前半の座標集合の和と全単射である。
方針：切断点より大きい点を後半へ、小さい点を前半へ送る。
規約：和の左側が後半、右側が前半。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面の立方体を和の座標の立方体へ移す。 -/
def pathSplitCoordinateEquiv (S : Finset (Set.Ioo a b)) (j : S) :
    ↥(S.erase j.val) ≃
      ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) ⊕ ↥(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) where
  toFun t :=
    let v : S := ⟨t.val, Finset.mem_of_mem_erase t.property⟩
    if h : j.val.val < t.val.val then
      Sum.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S j.val.val b
        ⟨v, ⟨h, t.val.property.2⟩⟩)
    else
      Sum.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S a j.val.val
        ⟨v, ⟨t.val.property.1, lt_of_le_of_ne (le_of_not_gt h)
          (fun he ↦ (Finset.mem_erase.mp t.property).1 (Subtype.ext he))⟩⟩)
  invFun := Sum.elim
    (fun t ↦
      let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S j.val.val b).symm t
      ⟨v.val.val, Finset.mem_erase.mpr ⟨fun h ↦ by
        have he := congrArg Subtype.val h
        have hv := v.property.1
        rw [he] at hv
        exact lt_irrefl _ hv, v.val.property⟩⟩)
    (fun t ↦
      let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S a j.val.val).symm t
      ⟨v.val.val, Finset.mem_erase.mpr ⟨fun h ↦ by
        have he := congrArg Subtype.val h
        have hv := v.property.2
        rw [he] at hv
        exact lt_irrefl _ hv, v.val.property⟩⟩)
  left_inv t := by
    dsimp only
    split_ifs with h
    · simp only [Sum.elim_inl, OrderIso.symm_apply_apply]
    · simp only [Sum.elim_inr, OrderIso.symm_apply_apply]
  right_inv t := by
    cases t with
    | inl t =>
      dsimp only [Sum.elim_inl]
      rw [dite_eq_left ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S j.val.val b).symm t).property.1]
      exact congrArg Sum.inl ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S j.val.val b).apply_symm_apply t)
    | inr t =>
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right
        (not_lt.mpr ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S a j.val.val).symm t).property.2.le)]
      exact congrArg Sum.inr ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso S a j.val.val).apply_symm_apply t)

/-- 概要：後半座標を元に戻しても点の値は同じである。
方針：区間の座標の逆順序同型の値の保存を使う。
規約：後半は和の左側。
使われ方：HA 1.3.1.16 の後半の Path の点集合と向きの比較。 -/
lemma pathSplitCoordinateEquiv_symm_inl_val (S : Finset (Set.Ioo a b)) (j : S)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b) :
    ((pathSplitCoordinateEquiv S j).symm (Sum.inl t)).val.val = t.val.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso_symm_val S j.val.val b t

/-- 概要：前半座標を元に戻しても点の値は同じである。
方針：区間の座標の逆順序同型の値の保存を使う。
規約：前半は和の右側。
使われ方：HA 1.3.1.16 の前半の Path の点集合と向きの比較。 -/
lemma pathSplitCoordinateEquiv_symm_inr_val (S : Finset (Set.Ioo a b)) (j : S)
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val) :
    ((pathSplitCoordinateEquiv S j).symm (Sum.inr t)).val.val = t.val.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalCoordinateIso_symm_val S a j.val.val t

/-- 概要：切断点を除いた座標数は後半と前半の内部点数の和である。
方針：座標の全単射で有限集合の濃度を比較する。
規約：切断点自身はどちらの開区間にも含まない。
使われ方：Kerodon 2.5.9（Tag 00SC） の合成面の次数を左右の次数の和に同定する。 -/
lemma card_pathSplitCoordinates (S : Finset (Set.Ioo a b)) (j : S) :
    (S.erase j.val).card =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S j.val.val b).card + (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathIntervalSet S a j.val.val).card := by
  simpa using Fintype.card_congr (pathSplitCoordinateEquiv S j)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
