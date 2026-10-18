module

public import SerrePositivity.EInfinity.BarrattEccles.ShufflePaths
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# 格子経路の shuffle 置換と符号

概要：Berger–Fresse §1.1.3 の水平辺・垂直辺の並べ替えによる符号を定義する。
方針：各辺集合を昇順に番号付けし、水平辺を先、垂直辺を後に並べる置換を作る。
規約：この置換は原典の並べ替えの逆であるが signature は逆元で変わらない。
使われ方：Barratt–Eccles の合成の shuffle 和の係数となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：水平辺と垂直辺の各番号を経路中の辺番号へ戻す（Berger–Fresse §1.1.3）。
方針：二つの辺集合の昇順の同値を、和の型の二成分に用いる。
規約：左成分が水平辺、右成分が垂直辺。
使われ方：shuffle 置換の構成と各ブロックの単調性を与える。 -/
def ShufflePath.segmentEnumeration {p q : ℕ} (s : ShufflePath p q) :
    Fin p ⊕ Fin q ≃ Fin (p + q) where
  toFun x := match x with
    | Sum.inl i => (s.val.orderIsoOfFin s.property i).val
    | Sum.inr j => (s.valᶜ.orderIsoOfFin s.compl_card j).val
  invFun k := if hk : k ∈ s.val then
      Sum.inl ((s.val.orderIsoOfFin s.property).symm ⟨k, hk⟩)
    else Sum.inr ((s.valᶜ.orderIsoOfFin s.compl_card).symm
      ⟨k, Finset.mem_compl.mpr hk⟩)
  left_inv x := by
    rcases x with i | j
    · dsimp only
      rw [dite_eq_left (s.val.orderIsoOfFin s.property i).property]
      exact congrArg Sum.inl ((s.val.orderIsoOfFin s.property).symm_apply_apply i)
    · have hj : (s.valᶜ.orderIsoOfFin s.compl_card j).val ∉ s.val :=
        Finset.mem_compl.mp (s.valᶜ.orderIsoOfFin s.compl_card j).property
      dsimp only
      rw [dite_eq_right hj]
      exact congrArg Sum.inr ((s.valᶜ.orderIsoOfFin s.compl_card).symm_apply_apply j)
  right_inv k := by
    dsimp only
    split_ifs with hk
    · exact congrArg Subtype.val ((s.val.orderIsoOfFin s.property).apply_symm_apply ⟨k, hk⟩)
    · exact congrArg Subtype.val ((s.valᶜ.orderIsoOfFin s.compl_card).apply_symm_apply
        ⟨k, Finset.mem_compl.mpr hk⟩)

/-- 概要：shuffle 置換は最初の p 個を水平辺へ送る（Berger–Fresse §1.1.3）。
方針：Fin(p+q) の和分解を辺の昇順列挙へ合成する。
規約：残りの q 個は垂直辺へ送る。
使われ方：経路の signature を定義する。 -/
def ShufflePath.permutation {p q : ℕ} (s : ShufflePath p q) : Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.symm.trans s.segmentEnumeration

/-- 概要：shuffle 置換の水平成分は水平辺の昇順列挙である（Berger–Fresse §1.1.3）。
方針：有限和の左成分で置換を評価する。
規約：辺番号の順序は保たれる。
使われ方：shuffle の符号と水平辺の対応を計算する。 -/
@[simp] lemma ShufflePath.permutation_castAdd {p q : ℕ} (s : ShufflePath p q) (i : Fin p) :
    s.permutation (Fin.castAdd q i) = (s.val.orderIsoOfFin s.property i).val := by
  simp [ShufflePath.permutation, ShufflePath.segmentEnumeration]

/-- 概要：shuffle 置換の垂直成分は垂直辺の昇順列挙である（Berger–Fresse §1.1.3）。
方針：有限和の右成分で置換を評価する。
規約：辺番号の順序は保たれる。
使われ方：shuffle の符号と垂直辺の対応を計算する。 -/
@[simp] lemma ShufflePath.permutation_natAdd {p q : ℕ} (s : ShufflePath p q) (j : Fin q) :
    s.permutation (Fin.natAdd p j) = (s.valᶜ.orderIsoOfFin s.compl_card j).val := by
  simp [ShufflePath.permutation, ShufflePath.segmentEnumeration]

/-- 概要：shuffle 置換は水平辺の内部の順序を保つ（Berger–Fresse §1.1.3）。
方針：有限集合の昇順の同値の狭義単調性を使う。
規約：水平ブロックだけに制限した写像について述べる。
使われ方：置換が通常の (p,q)-shuffle であることを確認する。 -/
lemma ShufflePath.permutation_horizontal_strictMono {p q : ℕ} (s : ShufflePath p q) :
    StrictMono (fun i : Fin p => s.permutation (Fin.castAdd q i)) := by
  intro i j hij
  change s.permutation (Fin.castAdd q i) < s.permutation (Fin.castAdd q j)
  rw [s.permutation_castAdd, s.permutation_castAdd]
  exact (s.val.orderIsoOfFin s.property).strictMono hij

/-- 概要：shuffle 置換は垂直辺の内部の順序を保つ（Berger–Fresse §1.1.3）。
方針：垂直辺の昇順の同値の狭義単調性を使う。
規約：垂直ブロックだけに制限した写像について述べる。
使われ方：置換が通常の (p,q)-shuffle であることを確認する。 -/
lemma ShufflePath.permutation_vertical_strictMono {p q : ℕ} (s : ShufflePath p q) :
    StrictMono (fun j : Fin q => s.permutation (Fin.natAdd p j)) := by
  intro i j hij
  change s.permutation (Fin.natAdd p i) < s.permutation (Fin.natAdd p j)
  rw [s.permutation_natAdd, s.permutation_natAdd]
  exact (s.valᶜ.orderIsoOfFin s.compl_card).strictMono hij

/-- 概要：格子経路に対応する shuffle の符号（Berger–Fresse §1.1.3）。
方針：水平辺・垂直辺の並べ替えを表す置換の signature を取る。
規約：整数の単元、すなわち ±1 として持つ。
使われ方：shuffle 合成の有限和の各項を符号づける。 -/
def ShufflePath.sign {p q : ℕ} (s : ShufflePath p q) : ℤˣ := Equiv.Perm.sign s.permutation

end SerrePositivity.EInfinity.BarrattEccles
