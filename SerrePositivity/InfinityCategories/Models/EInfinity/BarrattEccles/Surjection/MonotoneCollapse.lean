module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapsePrefixes
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.Hom.Basic

/-!
模型。文献の定義との比較は後で
# 単位歩幅の単調写像による繰り返しと縮約

概要：Berger–Fresse §1.5.8 の経路座標で繰り返した置換列を元の列へ戻す。
方針：最初の一歩が静止なら共有先頭を省き、増加なら値域の先頭を一つ省いて帰納する。
規約：写像は端点を保ち、単調で一度に高々一だけ増える。
使われ方：圧縮外側行列を元の外側行列の連続重複縮約へ同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse

variable {α : Type*} [DecidableEq α]

/-- 概要：端点を保つ単位歩幅の単調写像で繰り返した列は同じ縮約を持つ（BF §1.5.8）。
方針：定義域の辺数で帰納し、最初の静止か増加かで列の先頭を処理する。
規約：元の値列自体にも連続重複を許す。
使われ方：shuffle の水平座標の繰り返しを圧縮して元の外側行列に戻す。 -/
lemma collapse_ofFn_orderHom (N P : ℕ) (f : Fin (N + 1) →o Fin (P + 1))
    (hzero : f 0 = 0) (hlast : f (Fin.last N) = Fin.last P)
    (hstep : ∀ i : Fin N, (f i.succ).val ≤ (f i.castSucc).val + 1)
    (g : Fin (P + 1) → α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn (fun k => g (f k))) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn g) := by
  induction N generalizing P with
  | zero =>
    have hp : P = 0 := by
      have hz := congrArg Fin.val hzero
      have hl := congrArg Fin.val hlast
      change (f 0).val = P at hl
      change (f 0).val = 0 at hz
      omega
    subst P
    simp only [List.ofFn_succ, List.ofFn_zero, hzero]
  | succ N ih =>
    let ft : Fin (N + 1) →o Fin (P + 1) :=
      ⟨fun k => f k.succ, fun a b h => f.monotone (by
        change a.val + 1 ≤ b.val + 1
        exact Nat.add_le_add_right h 1)⟩
    have hfirst : (f (0 : Fin (N + 1)).succ).val ≤ 1 := by
      have h := hstep (0 : Fin (N + 1))
      simpa only [Fin.castSucc_zero, hzero, Fin.val_zero, Nat.zero_add] using h
    by_cases hz : f (0 : Fin (N + 1)).succ = 0
    · have hftlast : ft (Fin.last N) = Fin.last P := hlast
      have hftstep (i : Fin N) : (ft i.succ).val ≤ (ft i.castSucc).val + 1 :=
        hstep i.succ
      have ht := ih P ft hz hftlast hftstep g
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn (fun k : Fin (N + 1) => g (f k.succ))) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn g) at ht
      conv_lhs => rw [List.ofFn_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, hzero]
      rw [ht]
      have hsource : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn g) =
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend (g 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn (fun j : Fin P => g j.succ))) := by
        rw [List.ofFn_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse]
      rw [hsource, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend_idempotent]
    · have hv : (f (0 : Fin (N + 1)).succ).val = 1 := by
        have hne : (f (0 : Fin (N + 1)).succ).val ≠ 0 := fun h => hz (Fin.ext h)
        omega
      cases P with
      | zero => have h := (f (0 : Fin (N + 1)).succ).isLt; omega
      | succ P =>
        have hpos (k : Fin (N + 1)) : 1 ≤ (f k.succ).val := by
          have h := f.monotone (show (0 : Fin (N + 1)).succ ≤ k.succ from by
            change 1 ≤ k.val + 1
            omega)
          change (f (0 : Fin (N + 1)).succ).val ≤ (f k.succ).val at h
          omega
        let fd : Fin (N + 1) →o Fin (P + 1) := {
          toFun := fun k => ⟨(f k.succ).val - 1, by have h := (f k.succ).isLt; omega⟩
          monotone' a b hab := by
            change (f a.succ).val - 1 ≤ (f b.succ).val - 1
            exact Nat.sub_le_sub_right (f.monotone (by
              change a.val + 1 ≤ b.val + 1
              exact Nat.add_le_add_right hab 1)) 1 }
        have hfdzero : fd 0 = 0 := by
          apply Fin.ext
          change (f (0 : Fin (N + 1)).succ).val - 1 = 0
          omega
        have hfdlast : fd (Fin.last N) = Fin.last P := by
          apply Fin.ext
          change (f (Fin.last (N + 1))).val - 1 = P
          rw [hlast]
          rfl
        have hfdstep (i : Fin N) : (fd i.succ).val ≤ (fd i.castSucc).val + 1 := by
          have h := hstep i.succ
          have hp := hpos i.castSucc
          have hq := hpos i.succ
          change (f i.succ.succ).val - 1 ≤ (f i.castSucc.succ).val - 1 + 1
          change (f i.succ.succ).val ≤ (f i.castSucc.succ).val + 1 at h
          omega
        let gt : Fin (P + 1) → α := fun j => g j.succ
        have htail : List.ofFn (fun k : Fin (N + 1) => g (f k.succ)) =
            List.ofFn (fun k => gt (fd k)) := by
          apply congrArg List.ofFn
          funext k
          apply congrArg g
          apply Fin.ext
          change (f k.succ).val = (f k.succ).val - 1 + 1
          have h := hpos k
          omega
        conv_lhs => rw [List.ofFn_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse, hzero]
        rw [htail, ih P fd hfdzero hfdlast hfdstep gt]
        conv_rhs => rw [List.ofFn_succ, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse
