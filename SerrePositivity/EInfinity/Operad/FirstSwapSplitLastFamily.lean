module

public import SerrePositivity.EInfinity.Operad.TensorFamilySplitLastTransport

/-!
# 先頭二入力を交換した族と最後の分離

概要：Berger–Moerdijk §1 の先頭交換後の最後の因子の分離を具体的な入力族で比較する。
方針：交換した先頭二入力と元の尾を Fin.cases で記述し、始域・終域を同定する。
規約：先頭二入力以外の順序を保つ。
使われ方：末尾を固定する隣接交換と分離の可換性の先頭の場合に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：先頭二入力を交換して残りを保つ複体の入力族（Berger–Moerdijk §1）。
方針：二回の Fin.cases で交換した先頭二つと元の尾を記述する。
規約：元の族の長さは n+2。
使われ方：先頭交換の後の分離を再帰で展開する。 -/
def tensorFamilyFirstSwapFamily (n : ℕ) (V : Fin (n + 2) → Complex A) :
    Fin (n + 2) → Complex A :=
  Fin.cases (V 1) (Fin.cases (V 0) (fun i => V i.succ.succ))

attribute [local implicit_reducible] tensorFamilyFirstSwapFamily

/-- 概要：具体的な先頭交換の族は先頭の隣接互換による引き戻しと一致する（Berger–Moerdijk §1）。
方針：先頭二位置と残りの位置で互換を評価する。
規約：族全体の等式として比較する。
使われ方：最後の分離の入力族の移送の比較に用いる。 -/
lemma tensorFamilyFirstSwapFamily_eq (n : ℕ) (V : Fin (n + 2) → Complex A) :
    tensorFamilyFirstSwapFamily n V =
      fun i => V (adjacentTransposition (0 : Fin (n + 1)) i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change V 1 = V (adjacentTransposition (0 : Fin (n + 1)) 0)
    rw [adjacentFirst_zero]
  · refine Fin.cases ?_ (fun j => ?_) j
    · change V 0 = V (adjacentTransposition (0 : Fin (n + 1)) 1)
      rw [adjacentFirst_one]
    · change V j.succ.succ = V (adjacentTransposition (0 : Fin (n + 1)) j.succ.succ)
      rw [adjacentFirst_tail]

/-- 概要：具体的な先頭交換の族のテンソル対象は交換した二因子と元の尾で表せる（Berger–Moerdijk §1）。
方針：有限テンソルの先頭二段を展開する。
規約：尾の n 因子の括弧と順序を保つ。
使われ方：先頭二因子の交換の構造射の終域に同定する。 -/
lemma tensorFamilyFirstSwapFamily_source_obj (n : ℕ) (V : Fin (n + 2) → Complex A) :
    tensorFamily (n + 2) (tensorFamilyFirstSwapFamily n V) =
      V 1 ⊗ (V 0 ⊗ tensorFamily n (fun i => V i.succ.succ)) := by
  simp only [tensorFamily, tensorFamilyFirstSwapFamily, Fin.cases_zero, Fin.cases_succ]

/-- 概要：最後の因子を除いた具体的な先頭交換の族は前半の先頭交換に一致する（Berger–Moerdijk §1）。
方針：前半の先頭二つと残りで場合分けする。
規約：族の全長は n+3。
使われ方：最後の分離の終域の前半を展開する。 -/
lemma tensorFamilyFirstSwapFamily_prefix (n : ℕ) (V : Fin (n + 3) → Complex A)
    (i : Fin (n + 2)) :
    tensorFamilyFirstSwapFamily (n + 1) V i.castSucc =
      tensorFamilyFirstSwapFamily n (fun j => V j.castSucc) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl

/-- 概要：具体的な先頭交換の族は最後の因子を保つ（Berger–Moerdijk §1）。
方針：最後の位置は先頭二つの後にあることを使って評価する。
規約：族の長さは少なくとも三。
使われ方：交換後の最後の分離の右の因子を同定する。 -/
lemma tensorFamilyFirstSwapFamily_last (n : ℕ) (V : Fin (n + 3) → Complex A) :
    tensorFamilyFirstSwapFamily (n + 1) V (Fin.last (n + 2)) = V (Fin.last (n + 2)) := by
  rfl

/-- 概要：具体的な先頭交換の最後の分離の終域は交換した先頭二因子を明示して表せる（Berger–Moerdijk §1）。
方針：前半と最後の因子の計算に前半の有限テンソルの展開を適用する。
規約：最後の因子を右側に分離する。
使われ方：一般のモノイダル圏の四因子の整合性へ接続する。 -/
lemma tensorFamilyFirstSwapFamily_output_obj (n : ℕ) (V : Fin (n + 3) → Complex A) :
    tensorFamily (n + 2) (fun i => tensorFamilyFirstSwapFamily (n + 1) V i.castSucc) ⊗
        tensorFamilyFirstSwapFamily (n + 1) V (Fin.last (n + 2)) =
      (V 1 ⊗ (V 0 ⊗ tensorFamily n (fun i => V i.castSucc.succ.succ))) ⊗
        V (Fin.last (n + 2)) := by
  simp only [tensorFamilyFirstSwapFamily_prefix, tensorFamilyFirstSwapFamily_last,
    tensorFamilyFirstSwapFamily_source_obj]
  rfl

end SerrePositivity.EInfinity
