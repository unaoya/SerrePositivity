module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexSubsetOrder
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Hom.Set

/-! # 元の閉区間部分集合の昇順列挙
概要：元の閉区間を部分集合として列挙すると、元の始点と局所頂点番号の和を回収。
方針：元の区間濃度と、同じ像を持つ厳密単調な有限列の一意性を使う。
規約：元の部分集合と全頂点番号を保持。使われ方：全区間の実部分集合生成射の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の閉区間の頂点濃度は、元の区間長に一を加えた値。 -/
lemma simplexClosedInterval_card {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b) :
    (Finset.Icc a b).card = b.val - a.val + 1 := by
  rw [Fin.card_Icc]
  have ha : a.val ≤ b.val := hab
  omega

/-- 元の厳密区間の閉区間部分集合は、元の両端の少なくとも二頂点を持つ。 -/
lemma simplexClosedInterval_two {N : ℕ} (a b : Fin (N + 1)) (hab : a < b) :
    2 ≤ (Finset.Icc a b).card := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card a b hab.le]
  have ha : a.val < b.val := hab
  omega

/-- 元の閉区間部分集合の最小頂点は、同じ元の始点。 -/
lemma simplexClosedInterval_min {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b)
    (h : (Finset.Icc a b).Nonempty) : a = (Finset.Icc a b).min' h := by
  apply le_antisymm
  · exact (Finset.mem_Icc.mp (Finset.min'_mem _ h)).1
  · exact Finset.min'_le _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)

/-- 元の閉区間部分集合の最大頂点は、同じ元の終点。 -/
lemma simplexClosedInterval_max {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b)
    (h : (Finset.Icc a b).Nonempty) : b = (Finset.Icc a b).max' h := by
  apply le_antisymm
  · exact Finset.le_max' _ _ (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
  · exact (Finset.mem_Icc.mp (Finset.max'_mem _ h)).2

/-- 元の閉区間部分集合の全昇順頂点は、同じ始点に局所番号を加えた値。 -/
lemma simplexSubsetOrder_closedInterval_val {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b)
    (hI : 2 ≤ (Finset.Icc a b).card) (v : Fin ((Finset.Icc a b).card - 1 + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (Finset.Icc a b) hI v).val = a.val + v.val := by
  have hc := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card a b hab
  let g : Fin ((Finset.Icc a b).card - 1 + 1) → Fin (N + 1) :=
    fun j => ⟨a.val + j.val, by
      have hj := j.isLt
      have hb := b.isLt
      have ha : a.val ≤ b.val := hab
      omega⟩
  have hg : StrictMono g := by
    intro i j h
    change a.val + i.val < a.val + j.val
    exact Nat.add_lt_add_left h _
  have hf : StrictMono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (Finset.Icc a b) hI) :=
    ((Finset.Icc a b).orderEmbOfFin (show (Finset.Icc a b).card =
      (Finset.Icc a b).card - 1 + 1 by omega)).strictMono
  have hr : Set.range g = (Finset.Icc a b : Set (Fin (N + 1))) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      apply Finset.mem_Icc.mpr
      constructor
      · change a.val ≤ a.val + j.val
        omega
      · change a.val + j.val ≤ b.val
        have hj := j.isLt
        omega
    · intro hx
      have hax : a.val ≤ x.val := (Finset.mem_Icc.mp hx).1
      have hxb : x.val ≤ b.val := (Finset.mem_Icc.mp hx).2
      refine ⟨⟨x.val - a.val, by omega⟩, ?_⟩
      apply Fin.ext
      change a.val + (x.val - a.val) = x.val
      omega
  have he := hf.eq_of_range_eq hg ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_range (Finset.Icc a b) hI).trans hr.symm)
  exact congrArg Fin.val (congrFun he v)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexClosedInterval_card := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexClosedInterval_max := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_max

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexClosedInterval_min := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_min

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexClosedInterval_two := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_two

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexSubsetOrder_closedInterval_val := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_closedInterval_val
