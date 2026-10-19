module

public import SerrePositivity.EInfinity.IntervalCuts.NestedFamilyBlocks

/-!
# 辺・頂点入力の共通の有限切断添字

概要：Berger–Fresse §2.2.6 の辺入力と次数零の頂点入力を同じ有限添字で表す。
方針：辺は非零切断点 some q、頂点は内側語次数零の none とする。
規約：元の区間面は零頂点・一頂点・辺の三つ、arity 零も含む。
使われ方：実際の内側余演算を二段作用の有限和へ代入する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：指定面入力の非零項の条件（BF §2.2.6）。
方針：辺入力の切断点と、頂点入力の次数零条件を区別する。
規約：none は頂点入力だけ。
使われ方：内側余演算の有限和の共通添字。 -/
def FaceCutValid {n e : ℕ} (v : BasisWord n e) (s : Simplex) (a : Option (Fin (n + e))) : Prop :=
  match a with
  | some q => s = edge ∧ EdgeNondegenerate v.val q
  | none => s ≠ edge ∧ e = 0

/-- 概要：面入力の非零項条件は有限に判定できる（BF §2.2.6）。
方針：Option の場合を分け、既存の辺切断判定を使う。
規約：非計算的な選択を使わない。
使われ方：辺・頂点を統一した有限型を計算する。 -/
instance decidableFaceCutValid {n e : ℕ} (v : BasisWord n e) (s : Simplex) :
    DecidablePred (FaceCutValid v s) := by
  intro a
  cases a <;> unfold FaceCutValid <;> infer_instance

/-- 概要：指定面入力の全非零切断の有限型（BF §2.2.6）。
方針：Option の有限型から非零項条件を満たす部分型を取る。
規約：内側語次数が正の頂点入力では空型。
使われ方：実際の cochainAction の辺・頂点値の共通有限和。 -/
abbrev FaceCut {n e : ℕ} (v : BasisWord n e) (s : Simplex) :=
  {a : Option (Fin (n + e)) // FaceCutValid v s a}

namespace FaceCut

variable {n e : ℕ} {v : BasisWord n e} {s : Simplex}

/-- 概要：面切断の全出力族（BF §2.2.6）。
方針：辺では既存の切断出力、頂点では同じ頂点の一定族を返す。
規約：内側入力の順序を保持する。
使われ方：有限和の実際の面テンソル値。 -/
def output (a : FaceCut v s) (j : Fin n) : Simplex :=
  match a.val with
  | none => s
  | some q => edgeOutput v q j

/-- 概要：面切断の整数係数（BF §2.2.4–6）。
方針：辺では元の切断符号、頂点では一を使う。
規約：係数環へ移す前の整数値。
使われ方：二段作用の有限和で内側符号を保持する。 -/
def coefficient (a : FaceCut v s) : ℤ :=
  match a.val with
  | none => 1
  | some q => edgeSign v.val q

/-- 概要：面切断の全出力次数は語次数と入力面次数の和（BF §2.2.3）。
方針：辺切断の次数公式と頂点入力の次数零条件を使う。
規約：内側 arity 零も含む。
使われ方：実際の区間余演算の整数次数を有限和全体で揃える。 -/
lemma output_tupleDegree (a : FaceCut v s) : tupleDegree n a.output = e + simplexDegree s := by
  have H := a.property
  cases ha : a.val with
  | none =>
    rw [ha] at H
    have hd : simplexDegree s = 0 := by
      rw [simplexDegree_eq_edge_indicator, ite_eq_right H.1]
    simp only [output, ha, tupleDegree_eq_sum, hd, Finset.sum_const_zero, H.2, Nat.add_zero]
  | some q =>
    rw [ha] at H
    have hf : a.output = edgeOutput v q := by
      funext j
      simp only [output, ha]
    rw [hf, edgeOutput_tupleDegree v q H.2, H.1, simplexDegree_edge]

/-- 概要：辺入力の面切断は既存の非零辺切断と同値（BF §2.2.6）。
方針：none を排除し、some の切断点と非零性を取り出す。
規約：両方向とも実際の有限切断点を保つ。
使われ方：辺成分の既存の非零切断和を共通添字へ移す。 -/
def edgeEquiv (v : BasisWord n e) : FaceCut v edge ≃
    {q : Fin (n + e) // EdgeNondegenerate v.val q} where
  toFun a := match ha : a.val with
    | none => False.elim (by have H := a.property; rw [ha] at H; exact H.1 rfl)
    | some q => ⟨q, by have H := a.property; rw [ha] at H; exact H.2⟩
  invFun q := ⟨some q.val, rfl, q.property⟩
  left_inv a := by
    rcases a with ⟨a, h⟩
    cases a with
    | none => exact False.elim (h.1 rfl)
    | some q => rfl
  right_inv q := by rfl

/-- 概要：頂点入力の正次数語には非零面切断がない（BF §2.2.6）。
方針：none の次数零条件と some の辺入力条件をそれぞれ排除する。
規約：入力面は任意の非辺。
使われ方：実際の正次数語の頂点余演算の零値を空和へ移す。 -/
lemma isEmpty_of_nonedge_of_degree_ne_zero (v : BasisWord n e) (s : Simplex)
    (hs : s ≠ edge) (he : e ≠ 0) : IsEmpty (FaceCut v s) := by
  refine ⟨fun a => ?_⟩
  have H := a.property
  cases ha : a.val with
  | none => rw [ha] at H; exact he H.2
  | some q => rw [ha] at H; exact hs H.1

/-- 概要：非辺・次数零入力の面切断は一つだけ（BF §2.2.6）。
方針：some を排除して唯一の none と一元型を対応させる。
規約：辺ではない条件と語次数零を明示する。
使われ方：実際の頂点余演算の一項を共通有限和へ移す。 -/
def vertexEquiv (v : BasisWord n e) (s : Simplex) (hs : s ≠ edge) (he : e = 0) :
    FaceCut v s ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨none, hs, he⟩
  left_inv a := by
    apply Subtype.ext
    have H := a.property
    cases ha : a.val with
    | none => rfl
    | some q => rw [ha] at H; exact False.elim (hs H.1)
  right_inv u := by cases u; rfl

end FaceCut

end SerrePositivity.EInfinity.IntervalCuts
