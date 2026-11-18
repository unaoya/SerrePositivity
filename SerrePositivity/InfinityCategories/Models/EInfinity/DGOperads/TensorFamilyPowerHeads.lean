module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowers
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentGenerators
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerFirstBlockSwap

/-!
模型。文献の定義との比較は後で
# テンソル冪の有限族の先頭二ブロック

概要：Berger–Moerdijk §1 の有限テンソル族の連結を先頭二つのブロックで展開する。
方針：先頭から二回連結し、総和の移送を一つにまとめる。
規約：複体の微分とテンソル冪の対称性は既存の規約に従う。
使われ方：先頭の隣接交換と全入力への連結の両立に使う。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

/-- 概要：有限族の総和を先頭二つと残りに分ける（Berger–Moerdijk §1）。
方針：有限和の先頭の分離を二回行う。
規約：残りのブロックの総和は右括弧に含める。
使われ方：二つの先頭ブロックの連結の終域を比較する。 -/
lemma tensorFamily_sum_two (n : ℕ) (s : Fin (n + 2) → ℕ) :
    (∑ i, s i) = s 0 + (s 1 + ∑ i : Fin n, s i.succ.succ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  rfl

/-- 概要：二つの先頭ブロックの連結を展開する（Berger–Moerdijk §1）。
方針：有限族の連結を二回展開し、総和の移送を連結の自然性で整理する。
規約：終域の長さを先頭二つと残りの右括弧の和に移す。
使われ方：先頭のブロック交換を三因子の交換の式に接続する。 -/
@[reassoc]
lemma tensorPowerFamilyIso_two (K : Complex A) (n : ℕ) (s : Fin (n + 2) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 2) s).hom ≫
        eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_two n s)) =
      (power K (s 0) ◁ (power K (s 1) ◁
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ.succ)).hom)) ≫
        (power K (s 0) ◁
          (appendIso K (s 1) (∑ i : Fin n, s i.succ.succ)).hom) ≫
        (appendIso K (s 0) (s 1 + ∑ i : Fin n, s i.succ.succ)).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
    whiskerLeft_comp, Category.assoc]
  rw [appendIso_index_right_assoc K (s 0)
    (Fin.sum_univ_succ (fun i : Fin (n + 1) => s i.succ)).symm]
  simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：先頭交換後の総和を交換した二つと残りに分ける（Berger–Moerdijk §1）。
方針：総和の先頭二つの分離と隣接交換の入力位置の計算を使う。
規約：残りの入力位置は固定される。
使われ方：交換後の連結の終域を三ブロックの交換の終域と同定する。 -/
lemma tensorFamily_sum_firstSwap (n : ℕ) (s : Fin (n + 2) → ℕ) :
    (∑ i, s (adjacentTransposition (0 : Fin (n + 1)) i)) =
      s 1 + (s 0 + ∑ i : Fin n, s i.succ.succ) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_two]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_one, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_tail]

/-- 概要：等しい添字族の連結は同じ対象への移送後に一致する（Berger–Moerdijk §1）。
方針：添字族の等式で同一視し、対象の等式の証明の一意性を使う。
規約：始域と終域の両方の比較の等式を明示する。
使われ方：隣接互換と具体的な入力族の表示を連結の射で比較する。 -/
lemma tensorPowerFamilyIso_compare (K : Complex A) (n : ℕ) {s t : Fin n → ℕ} (h : s = t)
    {S T : Complex A}
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (s i)) = S)
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (t i)) = S)
    (hsp : power K (∑ i, s i) = T) (htp : power K (∑ i, t i) = T) :
    eqToHom ht.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n t).hom ≫ eqToHom htp =
      eqToHom hs.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom ≫ eqToHom hsp := by
  subst t
  rfl

/-- 概要：等しい添字族の連結を元の始域に移して比較する（Berger–Moerdijk §1）。
方針：添字族の等式で同一視してから恒等の移送を消す。
規約：終域だけは任意の同じ対象へ移す。
使われ方：具体的な複体の定義を展開せずに先頭交換の移送を計算する。 -/
lemma tensorPowerFamilyIso_compare_source (K : Complex A) (n : ℕ)
    {s t : Fin n → ℕ} (h : s = t) {T : Complex A}
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (t i)) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (s i)))
    (hsp : power K (∑ i, s i) = T) (htp : power K (∑ i, t i) = T) :
    eqToHom ht.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n t).hom ≫ eqToHom htp =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom ≫ eqToHom hsp := by
  subst t
  simp only [eqToHom_refl, Category.id_comp]

/-- 概要：先頭交換の具体的な添字族は先頭を二番目へ送る（Berger–Moerdijk §1）。
方針：隣接互換との比較を使う。
規約：入力位置は 0 始まり。
使われ方：連結の展開で添字族全体を展開せずに先頭を計算する。 -/
lemma tensorFirstSwapIndex_zero (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex n 0 = 1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex_eq]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_zero n

/-- 概要：先頭交換の具体的な添字族は二番目を先頭へ送る（Berger–Moerdijk §1）。
方針：隣接互換との比較を使う。
規約：少なくとも二つの入力を持つ。
使われ方：連結の展開で具体的な添字族の二番目を計算する。 -/
lemma tensorFirstSwapIndex_one (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex n 1 = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex_eq]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_one n

/-- 概要：先頭交換の具体的な添字族は三番目以降を固定する（Berger–Moerdijk §1）。
方針：隣接互換との比較を使う。
規約：残りの入力を二回の succ で表す。
使われ方：連結の展開で残りの入力族を同一視する。 -/
lemma tensorFirstSwapIndex_tail (n : ℕ) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex n i.succ.succ = i.succ.succ := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex_eq]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_tail n i

/-- 概要：先頭二つの長さを交換した具体的な有限族（Berger–Moerdijk §1）。
方針：先頭二つと残りを cases で与える。
規約：残りの入力の順序は保持する。
使われ方：先頭交換の対象の移送を小さい補題で計算する。 -/
def tensorPowerFirstSwapFamily (n : ℕ) (s : Fin (n + 2) → ℕ) : Fin (n + 2) → ℕ :=
  fun i => Fin.cases (s 1) (fun j => Fin.cases (s 0) (fun k => s k.succ.succ) j) i

/-- 概要：具体的な交換族は隣接互換による引き戻しに等しい（Berger–Moerdijk §1）。
方針：先頭、二番目、残りの入力で比較する。
規約：先頭の隣接互換を用いる。
使われ方：連結の添字族の比較補題に適用する。 -/
lemma tensorPowerFirstSwapFamily_eq (n : ℕ) (s : Fin (n + 2) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily n s =
      (fun i => s (adjacentTransposition (0 : Fin (n + 1)) i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_zero n).symm
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact congrArg s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_one n).symm
    · exact congrArg s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.adjacentFirst_tail n j).symm

/-- 概要：具体的な交換族の有限テンソルを先頭と残りで表す（Berger–Moerdijk §1）。
方針：有限テンソルの定義を二回評価する。
規約：最後の族の長さは n。
使われ方：連結の始域の比較を独立した等式として保持する。 -/
lemma tensorPowerFirstSwapFamily_obj (K : Complex A) (n : ℕ) (s : Fin (n + 2) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i => power K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily n s i)) =
      power K (s 1) ⊗ (power K (s 0) ⊗
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (s i.succ.succ))) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily, Fin.cases_zero, Fin.cases_succ]

/-- 概要：具体的な交換族の総和を先頭と残りで表す（Berger–Moerdijk §1）。
方針：有限和の先頭の分離を二回適用する。
規約：総和は右括弧で記述する。
使われ方：連結の終域の比較を複体の型検査から分離する。 -/
lemma tensorPowerFirstSwapFamily_sum (n : ℕ) (s : Fin (n + 2) → ℕ) :
    (∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily n s i) = s 1 + (s 0 + ∑ i : Fin n, s i.succ.succ) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_two n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFirstSwapFamily n s)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
