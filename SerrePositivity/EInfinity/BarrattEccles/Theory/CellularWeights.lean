module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Barratt–Eccles の準自由セルに付ける重み

## 概要
セルの微分を有限個の単項式で書いたとき、各項の総重みがそのセルより小さくなる。

## 方針
先に付加したセルへの整礎再帰で、有限個の単項式の総重みの最大値に一を加える。

## 規約
各単項式で同じ入力が複数回現れれば、その回数だけ重みを加える。

## 使われ方
HA §3.2.2 の係数拡大と §3.2.4.7 の余積比較に使う重みのフィルトレーション。
-/

@[expose] public section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

variable {ι : Type u} {earlier : ι → ι → Prop}
  (wf : WellFounded earlier)
  (terms : ∀ i, Finset (List {j : ι // earlier j i}))

/-- セルの微分の各単項式より大きくなるように選んだ重み。 -/
def cellularWeight : ι → ℕ :=
  wf.fix fun i w =>
    (terms i).sup (fun m => (m.map fun j => w j.val j.property).sum) + 1

/-- 各セルの重みを、微分に現れる先行セルの重みで計算する。 -/
lemma cellularWeight_eq (i : ι) :
    cellularWeight wf terms i =
      (terms i).sup (fun m => (m.map fun j => cellularWeight wf terms j.val).sum) + 1 := by
  exact WellFounded.fix_eq wf
    (fun i w => (terms i).sup (fun m => (m.map fun j => w j.val j.property).sum) + 1) i

/-- 微分の各単項式の総重みは元のセルの重みより小さい。 -/
lemma differentialTerm_weight_lt {i : ι} {m : List {j : ι // earlier j i}}
    (hm : m ∈ terms i) :
    (m.map fun j => cellularWeight wf terms j.val).sum < cellularWeight wf terms i := by
  rw [cellularWeight_eq]
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun w => (w.map fun j => cellularWeight wf terms j.val).sum) hm)

/-- 空の微分を持つセルも正の重みを持つ。 -/
lemma cellularWeight_pos (i : ι) : 0 < cellularWeight wf terms i := by
  rw [cellularWeight_eq]
  exact Nat.zero_lt_succ _

end SerrePositivity.EInfinity.BarrattEccles
