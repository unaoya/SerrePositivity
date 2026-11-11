module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinear
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedDeletion

/-! # 右 pinched 線形方程式の整合性

概要：線形右辺の削除作用素との一致と、残差の微分の削除和を証明する。
方針：不適切な次数や空集合を零で全域化し、二重削除の相殺を適用する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：直接の線形ホーン充填。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：非空集合と適切な次数では成分を返し、それ以外は零を返す。
方針：指定次数の同じ Hom 加群に全ての部分集合の値をそろえる。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：二重削除の全域関数への適用。 -/
def componentOrZero {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ) :
    GradedHom A x y k :=
  if hJ : J.Nonempty then
    if hk : k = 1 - (J.card : ℤ) then f.component J k hJ hk else 0
  else 0

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (componentOrZero)


/-- 概要：適切な集合と次数での全域評価は元の成分。
方針：全ての条件分岐を正しい側で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：削除和と元の線形右辺の比較。 -/
lemma componentOrZero_eq {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    f.componentOrZero J k = f.component J k hJ hk := by
  simp only [componentOrZero, dite_eq_left hJ, dite_eq_left hk]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (componentOrZero_eq)


/-- 概要：空集合での全域評価は零。
方針：非空性の条件が偽であることを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：一点集合の線形右辺。 -/
lemma componentOrZero_empty {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (k : ℤ) :
    f.componentOrZero ∅ k = 0 := by simp [componentOrZero]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (componentOrZero_empty)


/-- 概要：線形方程式の右辺は全域評価の全頂点削除和。
方針：二点以上では各削除成分を比較し、一点以下では全ての削除集合が空であることを使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形右辺の二重削除の相殺。 -/
lemma rhs_eq_deleteSum {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    f.rhs J k hk = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum (fun K => f.componentOrZero K (k + 1)) J := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum
  by_cases hJ : 2 ≤ J.card
  · rw [dite_eq_left hJ]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j.val • f.component (J.erase j.val) (k + 1) _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j.val • f.componentOrZero (J.erase j.val) (k + 1)
    rw [componentOrZero_eq f (J.erase j.val) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
      (by have := Finset.card_erase_add_one j.property; omega)]
  · rw [dite_eq_right hJ]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have he : J.erase j = ∅ := by
      apply Finset.card_eq_zero.mp
      have := Finset.card_erase_add_one hj
      omega
    rw [he]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j • f.componentOrZero ∅ (k + 1) = 0
    rw [componentOrZero_empty, smul_zero]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (rhs_eq_deleteSum)


/-- 概要：一段小さい集合の線形右辺の符号付き和は零。
方針：全域化した削除和に戻し、その二乗が零であることを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形残差の微分の式。 -/
lemma sum_rhs_eq_zero {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    (∑ j : J, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j.val • f.rhs (J.erase j.val) (k + 1)
      (by have := Finset.card_erase_add_one j.property; omega)) = 0 := by
  simp only [rhs_eq_deleteSum]
  let F : Fin (n + 1) → GradedHom A x y (k + 1 + 1) := fun j =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j • _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum (fun K => f.componentOrZero K (k + 1 + 1)) (J.erase j)
  change (∑ j : J, F j.val) = 0
  rw [Finset.sum_coe_sort]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deleteSum_squared (fun K => f.componentOrZero K (k + 1 + 1)) J

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (sum_rhs_eq_zero)


/-- 概要：線形方程式の残差は微分と削除和の差。
方針：同じ次数 k+1 の二つの成分を引く。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：欠けた面の方程式を零残差として扱う。 -/
def residual {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) : GradedHom A x y (k + 1) :=
  differential A (f.component J k hJ hk) - f.rhs J k hk

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (residual)


/-- 概要：残差が零であることと線形方程式は同値。
方針：加法群で差が零であることを等式に直す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：ホーン充填の各面の方程式の受入条件。 -/
lemma residual_eq_zero_iff {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    f.residual J k hJ hk = 0 ↔ differential A (f.component J k hJ hk) = f.rhs J k hk := sub_eq_zero

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (residual_eq_zero_iff)


/-- 概要：線形右辺の微分は削除成分の微分の符号付き和。
方針：微分の有限和・符号スカラーへの分配を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形残差の整合性。 -/
lemma differential_rhs {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : 2 ≤ J.card) (hk : k = 1 - (J.card : ℤ)) :
    differential A (f.rhs J k hk) =
      ∑ j : J, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j.val • differential A
        (f.component (J.erase j.val) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
          (by have := Finset.card_erase_add_one j.property; omega)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.rhs, dite_eq_left hJ]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_units_smul _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (differential_rhs)


/-- 概要：線形右辺の微分は一段小さい残差の符号付き和。
方針：二重削除和が零であることを、微分の展開から差し引く。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：ホーンの欠けた面の方程式。 -/
lemma differential_rhs_residual {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : 2 ≤ J.card) (hk : k = 1 - (J.card : ℤ)) :
    differential A (f.rhs J k hk) =
      ∑ j : J, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j.val • f.residual (J.erase j.val) (k + 1)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
        (by have := Finset.card_erase_add_one j.property; omega) := by
  rw [differential_rhs f J k hJ hk]
  simp only [residual, smul_sub, Finset.sum_sub_distrib]
  rw [sum_rhs_eq_zero f J k hk, sub_zero]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (differential_rhs_residual)


/-- 概要：上位の削除和が零で他の削除面の残差が零なら、指定した削除面の方程式が従う。
方針：残差の削除和から唯一の項を取り出し、可逆な削除係数を消す。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3 の線形ホーン充填。使われ方：欠けた面の方程式の検証。 -/
lemma missing_equation {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : 2 ≤ J.card) (hk : k = 1 - (J.card : ℤ))
    (i : Fin (n + 1)) (hi : i ∈ J) (hrhs : f.rhs J k hk = 0)
    (hother : ∀ j : J, j.val ≠ i → f.residual (J.erase j.val) (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
      (by have := Finset.card_erase_add_one j.property; omega) = 0) :
    differential A (f.component (J.erase i) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ i hi)
      (by have := Finset.card_erase_add_one hi; omega)) =
      f.rhs (J.erase i) (k + 1) (by have := Finset.card_erase_add_one hi; omega) := by
  have hs := differential_rhs_residual f J k hJ hk
  have hzero : differential A (f.rhs J k hk) = 0 := by
    rw [hrhs]
    exact map_zero _
  rw [Finset.sum_eq_single (⟨i, hi⟩ : J)] at hs
  · have hz := hs.symm.trans hzero
    have he := congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J i)⁻¹ • t) hz
    apply (residual_eq_zero_iff f (J.erase i) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ i hi)
      (by have := Finset.card_erase_add_one hi; omega)).mp
    simpa only [smul_smul, inv_mul_cancel, one_smul, smul_zero] using he
  · intro j _ hji
    rw [hother j (fun he => hji (Subtype.ext he)), smul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (missing_equation)


/-- 概要：欠けた面の成分を明示解に選ぶと最上位の線形右辺は零。
方針：右辺を全頂点削除和へ戻し、指定面を分離した相殺を適用する。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3。使われ方：実際のホーン充填での最上位方程式。 -/
lemma rhs_eq_zero_of_deletionSolution {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (i : Fin (n + 1)) (hi : i ∈ J)
    (hsolution : f.componentOrZero (J.erase i) (k + 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution J i (fun j => f.componentOrZero (J.erase j) (k + 1))) :
    f.rhs J k hk = 0 := by
  rw [rhs_eq_deleteSum]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_eq_zero_of_deletionSolution J i hi
    (fun j => f.componentOrZero (J.erase j) (k + 1)) hsolution

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (rhs_eq_zero_of_deletionSolution)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
