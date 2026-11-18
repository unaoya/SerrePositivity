module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
模型。文献の定義との比較は後で
# 対称オペラッドの部分合成の入力位置

概要：Berger–Moerdijk §1 の置換と合成の両立に現れる入力位置を構成する。
方針：一つの位置を n 個の連続した入力に置き換え、その分解の同値を使う。
規約：位置は 0 始まり。n=0 の代入も含める。
使われ方：対称 dg オペラッドの等変性と結合則の型を定める。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：一つの入力を n 個に置き換えた入力集合の分解（Berger–Moerdijk §1）。
方針：挿入区間の前・中・後で添字を明示する。
規約：外側の arity は m+1、代入後は m+n。n=0 を許す。
使われ方：内側・外側の対称群の作用を代入後の対称群へ運ぶ。 -/
def operadInsertionEquiv (m n : ℕ) (i : Fin (m + 1)) :
    Fin (m + n) ≃ ({j : Fin (m + 1) // j ≠ i} ⊕ Fin n) where
  toFun x :=
    if h₁ : x.val < i.val then
      Sum.inl ⟨⟨x.val, by omega⟩, by
        intro h
        have hv : x.val = i.val := congrArg Fin.val h
        omega⟩
    else if h₂ : x.val < i.val + n then
      Sum.inr ⟨x.val - i.val, by omega⟩
    else
      Sum.inl ⟨⟨x.val + 1 - n, by omega⟩,
        by
          intro h
          have hv : x.val + 1 - n = i.val := congrArg Fin.val h
          omega⟩
  invFun x := match x with
    | Sum.inl j =>
      if h : j.val.val < i.val then ⟨j.val.val, by omega⟩
      else ⟨j.val.val + n - 1, by
        have hj : j.val.val ≠ i.val := fun h => j.property (Fin.ext h)
        omega⟩
    | Sum.inr j => ⟨i.val + j.val, by omega⟩
  left_inv x := by
    dsimp
    split_ifs <;> (try dsimp) <;> (try split_ifs) <;>
      apply Fin.ext <;> (try dsimp at *) <;> omega
  right_inv x := by
    rcases x with ⟨j, hj⟩ | j
    · dsimp
      have hne : j.val ≠ i.val := fun h => hj (Fin.ext h)
      split_ifs <;> (try dsimp at *) <;>
        (try simp_all only [Sum.inl.injEq, Subtype.ext_iff, Fin.ext_iff]) <;>
        (try dsimp at *) <;> omega
    · dsimp
      split_ifs <;>
        (try simp_all only [Sum.inr.injEq, Fin.ext_iff]) <;> omega

/-- 概要：代入した内側の入力の置換（Berger–Moerdijk §1）。
方針：挿入分解の内側の因子だけを置換し、同値で戻す。
規約：外側の残りの入力は固定する。
使われ方：対称オペラッドの内側等変性を述べる。 -/
def operadInnerPermutation (m n : ℕ) (i : Fin (m + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).trans
    ((Equiv.sumCongr (Equiv.refl _) τ).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).symm)

/-- 概要：外側の置換が代入していない入力へ誘導する同値（Berger–Moerdijk §1）。
方針：置換とその逆置換を、指定入力を除いた部分型へ制限する。
規約：除く位置 i は σ(i) へ送る。
使われ方：外側等変性の入力置換を構成する。 -/
def operadRemainingEquiv (m : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin (m + 1))) :
    {j : Fin (m + 1) // j ≠ i} ≃ {j : Fin (m + 1) // j ≠ σ i} where
  toFun j := ⟨σ j.val, fun h => j.property (σ.injective h)⟩
  invFun j := ⟨σ.symm j.val, fun h => j.property (by simpa using congrArg σ h)⟩
  left_inv j := Subtype.ext (σ.symm_apply_apply j.val)
  right_inv j := Subtype.ext (σ.apply_symm_apply j.val)

/-- 概要：外側の置換を代入後の入力集合へ延長する（Berger–Moerdijk §1）。
方針：残りの入力を σ で動かし、挿入区間の内部の順序を保つ。
規約：挿入区間は位置 i から位置 σ(i) へ移る。
使われ方：対称オペラッドの外側等変性を述べる。 -/
def operadOuterPermutation (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) : Equiv.Perm (Fin (m + n)) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).trans
    ((Equiv.sumCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m i σ) (Equiv.refl _)).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n (σ i)).symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
