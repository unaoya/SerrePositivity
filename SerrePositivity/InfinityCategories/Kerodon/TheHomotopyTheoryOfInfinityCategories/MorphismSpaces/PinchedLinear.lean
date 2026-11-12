module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex

/-! # 右 pinched 写像空間の線形単体

概要：非空有限部分集合 J ごとの次数 1−|J| の成分と線形削除方程式を定義する。
方針：成分族を A 加群にし、微分と符号付き削除和の等式で部分加群を切り出す。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）、N0.3 の cochain 符号。
使われ方：右 pinched Hom の全次数の線形表示と直接のホーン充填の模型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] (x y : D)

/-- 概要：非空部分集合に次数 1−|J| の射を割り当てる線形成分族。
方針：次数と等式を引数に取り、有限集合の削除での cast を避ける。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形単体の全成分。 -/
abbrev LinearData (n : ℕ) :=
  ∀ i : {i : Finset (Fin (n + 1)) × ℤ // i.1.Nonempty ∧ i.2 = 1 - (i.1.card : ℤ)},
    GradedHom A x y i.val.2

variable {A x y}

namespace LinearData

/-- 概要：線形成分族を有限集合と指定次数で評価する。
方針：非空性と次数の証明を成分の添字にまとめる。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：cast を伴わない成分の計算。 -/
def component {n : ℕ} (f : LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) : GradedHom A x y k := f ⟨(J, k), hJ, hk⟩

/-- 概要：二点以上の集合から一点を消しても非空。
方針：削除による濃度の一つの減少を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：削除項の成分の定義域。 -/
lemma erase_nonempty {n : ℕ} {J : Finset (Fin (n + 1))} (hJ : 2 ≤ J.card)
    (j : Fin (n + 1)) (hj : j ∈ J) : (J.erase j).Nonempty := by
  apply Finset.card_pos.mp
  have := Finset.card_erase_add_one hj
  omega

/-- 概要：線形方程式の右辺は全頂点を一つずつ消す符号付き和。
方針：濃度一の場合を零、濃度二以上の場合を削除和とする。
規約：Kerodon §4.6.5（Tag 01KW）、符号は j より大きい点の個数に一を加えた整数の negOnePow。
使われ方：先頭面を定値とした dg nerve の方程式。 -/
def rhs {n : ℕ} (f : LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) : GradedHom A x y (k + 1) :=
  if hJ : 2 ≤ J.card then
    ∑ j : J, (((J.filter (j.val < ·)).card : ℤ) + 1).negOnePow •
      f.component (J.erase j.val) (k + 1) (erase_nonempty hJ j.val j.property)
        (by have := Finset.card_erase_add_one j.property; omega)
  else 0

/-- 概要：零族の線形方程式の右辺は零。
方針：符号付き和の全項が零であることを使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：解の部分加群の零元。 -/
lemma rhs_zero {n : ℕ} (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (0 : LinearData A x y n).rhs J k hk = 0 := by
  simp [rhs, component]

/-- 概要：線形成分族の和に対して右辺は加法的。
方針：各削除項の符号スカラーの加法性と有限和の加法性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：解の部分加群の加法。 -/
lemma rhs_add {n : ℕ} (f g : LinearData A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hk : k = 1 - (J.card : ℤ)) :
    (f + g).rhs J k hk = f.rhs J k hk + g.rhs J k hk := by
  unfold rhs
  split_ifs
  · simp only [component, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  · exact (zero_add _).symm

/-- 概要：A スカラー倍に対して線形方程式の右辺は線形。
方針：符号の整数単位スカラーと A の作用の可換性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：解の部分加群のスカラー倍。 -/
lemma rhs_smul {n : ℕ} (c : A) (f : LinearData A x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    (c • f).rhs J k hk = c • f.rhs J k hk := by
  unfold rhs
  split_ifs
  · simp only [component, Pi.smul_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  · exact (smul_zero c).symm

end LinearData

variable (A x y)

/-- 概要：線形削除方程式を満たす成分族は A 部分加群をなす。
方針：微分と削除和がともに A 線形であることから零・加法・スカラー倍を保存する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：線形単体の加群構造。 -/
def linearSubmodule (n : ℕ) : Submodule A (LinearData A x y n) where
  carrier := {f | ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)),
    differential A (f.component J k hJ hk) = f.rhs J k hk}
  zero_mem' := by
    intro J k hJ hk
    change (homObject A D x y).d k (k + 1) 0 = _
    rw [map_zero, LinearData.rhs_zero]
  add_mem' := by
    intro f g hf hg J k hJ hk
    change (homObject A D x y).d k (k + 1) (f.component J k hJ hk + g.component J k hJ hk) = _
    rw [map_add]
    change differential A (f.component J k hJ hk) + differential A (g.component J k hJ hk) = _
    rw [hf J k hJ hk, hg J k hJ hk, LinearData.rhs_add]
  smul_mem' := by
    intro c f hf J k hJ hk
    change (homObject A D x y).d k (k + 1) (c • f.component J k hJ hk) = _
    rw [map_smul]
    change c • differential A (f.component J k hJ hk) = _
    rw [hf J k hJ hk, LinearData.rhs_smul]

/-- 概要：線形単体は線形削除方程式の解の A 加群。
方針：解の部分加群の台型を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の各次数の線形模型。 -/
abbrev LinearSimplex (n : ℕ) := ↥(linearSubmodule A x y n)

namespace LinearSimplex

variable {A x y}

/-- 概要：線形単体の各成分は指定された微分方程式を満たす。
方針：解の部分加群への所属条件を取り出す。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：直接の線形ホーン充填と dg nerve の単体への再構成。 -/
lemma equation {n : ℕ} (s : LinearSimplex A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    differential A (s.val.component J k hJ hk) = s.val.rhs J k hk := s.property J k hJ hk

/-- 概要：一点集合の成分は閉元である。
方針：濃度一では削除和が零になることを方程式に代入する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：線形単体の各頂点の閉零射。 -/
lemma closed_singleton {n : ℕ} (s : LinearSimplex A x y n) (a : Fin (n + 1)) :
    differential A (s.val.component {a} 0 (by simp) (by simp)) = 0 := by
  have he := s.equation {a} 0 (by simp) (by simp)
  simpa only [LinearData.rhs, Finset.card_singleton, show ¬ (2 ≤ 1) from by omega,
    dite_false] using he

end LinearSimplex

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
