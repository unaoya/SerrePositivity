module
public import SerrePositivity.KST.SConstruction.SimplexHAStrictIntervalOrder
public import SerrePositivity.KST.SConstruction.SimplexHASplitOrder
public import SerrePositivity.KST.SConstruction.SimplexHAOrderDimensionCast

/-! # 元の全区間 HA 列の厳密二区間への切断
概要：元の全区間の列を共有頂点で切り、元の左右区間の列を厳密に回収する。
方針：元の数値番号の加法と同じ次元等号移送を照合する。
規約：元の始点・切断頂点・終点を保持。使われ方：native HA 逆鎖射の合成保存。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の厳密二区間の全内部次元は、切断頂点を一つ加えた左右内部次元の和。 -/
lemma simplexHAStrictInterval_split_dimension {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    c.val - a.val - 1 = (b.val - a.val - 1) + 1 + (c.val - b.val - 1) := by
  have ha : a.val < b.val := hab
  have hb : b.val < c.val := hbc
  omega

/-- 元の列の次元移送は、元の全局所頂点番号を保つ。 -/
lemma simplexHAOrderDimensionCast_apply {N n m : ℕ} (h : n = m)
    (v : Fin (n + 1) ↪o Fin (N + 1)) (j : Fin (m + 1)) :
    simplexHAOrderDimensionCast h v j = v (Fin.cast (congrArg Nat.succ h.symm) j) := by
  cases h
  rfl

/-- 元の全区間の同じ切断用次元表示を持つ頂点列。 -/
def simplexHAStrictIntervalSplitOrder {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    Fin ((b.val - a.val - 1) + 1 + (c.val - b.val - 1) + 1) ↪o Fin (N + 1) :=
  simplexHAOrderDimensionCast (simplexHAStrictInterval_split_dimension a b c hab hbc)
    (simplexHAStrictIntervalOrder a c (hab.trans hbc))

/-- 元の切断用全区間列は、同じ始点に元の局所番号を加える。 -/
lemma simplexHAStrictIntervalSplitOrder_val {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c)
    (j : Fin ((b.val - a.val - 1) + 1 + (c.val - b.val - 1) + 1)) :
    (simplexHAStrictIntervalSplitOrder a b c hab hbc j).val = a.val + j.val := by
  unfold simplexHAStrictIntervalSplitOrder
  rw [simplexHAOrderDimensionCast_apply]
  rfl

/-- 元の切断用全区間列の始点は、元の同じ a。 -/
lemma simplexHAStrictIntervalSplitOrder_first {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) : simplexHAStrictIntervalSplitOrder a b c hab hbc 0 = a :=
  simplexHAOrderDimensionCast_first _ _

/-- 元の切断用全区間列の最後は、元の終点 c より厳密に左。 -/
lemma simplexHAStrictIntervalSplitOrder_last_lt {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    simplexHAStrictIntervalSplitOrder a b c hab hbc
      (Fin.last ((b.val - a.val - 1) + 1 + (c.val - b.val - 1))) < c :=
  lt_of_eq_of_lt (simplexHAOrderDimensionCast_last _ _)
    (simplexHAStrictIntervalOrder_last_lt a c (hab.trans hbc))

/-- 元の全区間の切断左列は、元の同じ厳密左区間の全頂点列。 -/
lemma simplexHAStrictIntervalSplitOrder_left {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    simplexHASplitLeft (b.val - a.val - 1) (c.val - b.val - 1)
        (simplexHAStrictIntervalSplitOrder a b c hab hbc) =
      simplexHAStrictIntervalOrder a b hab := by
  ext j
  exact simplexHAStrictIntervalSplitOrder_val a b c hab hbc _

/-- 元の全区間の切断点は、元の同じ共有頂点。 -/
lemma simplexHAStrictIntervalSplitOrder_cut {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    simplexHASplitCut (b.val - a.val - 1) (c.val - b.val - 1)
      (simplexHAStrictIntervalSplitOrder a b c hab hbc) = b := by
  apply Fin.ext
  have h := simplexHAStrictIntervalSplitOrder_val a b c hab hbc
    ⟨(b.val - a.val - 1) + 1, by omega⟩
  change _ = b.val
  exact h.trans (by
    change a.val + ((b.val - a.val - 1) + 1) = b.val
    have ha : a.val < b.val := hab
    omega)

/-- 元の全区間の切断右列は、元の同じ厳密右区間の全頂点列。 -/
lemma simplexHAStrictIntervalSplitOrder_right {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    simplexHASplitRight (b.val - a.val - 1) (c.val - b.val - 1)
        (simplexHAStrictIntervalSplitOrder a b c hab hbc) =
      simplexHAStrictIntervalOrder b c hbc := by
  ext j
  have h := simplexHAStrictIntervalSplitOrder_val a b c hab hbc
    ⟨(b.val - a.val - 1) + 1 + j.val, by have hj := j.isLt; omega⟩
  exact h.trans (by
    change a.val + ((b.val - a.val - 1) + 1 + j.val) = b.val + j.val
    have ha : a.val < b.val := hab
    omega)

end SerrePositivity.KST.SConstruction
