module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # 単体の方程式の削除部分

概要：単体の方程式の線形な削除部分を取り出し、それを二度適用した和が零であることを示す。
方針：内部点の有限集合を使い、斉次成分を不適切な添字では零とする補助関数で全域化する。
規約：HA Proposition 1.3.1.10。単体の表現は従来の有限部分集合のまま。
使われ方：主残差恒等式の二重削除項の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

namespace Index

/-- 概要：部分集合の指定端点の間にある内部点の集合。
方針：両側の狭義不等式で有限集合を filter する。
規約：HA Construction 1.3.1.6。使われ方：削除・切断の有限和の添字。 -/
def interior {α : Type*} [LinearOrder α] (I : Finset α) (a b : α) : Finset α :=
  I.filter (fun j => a < j ∧ j < b)

/-- 概要：内部点集合の形成は点の削除と可換。
方針：有限集合の filter と erase の交換を使う。
規約：HA Proposition 1.3.1.10。使われ方：二重削除の和を共通の内部点集合で表す。 -/
lemma interior_erase {α : Type*} [LinearOrder α] (I : Finset α) (a b j : α) :
    interior (I.erase j) a b = (interior I a b).erase j := by
  exact Finset.filter_erase _ _ _

/-- 概要：異なる二点の組の有限和は、一点ずつ選び第二点で第一点を除く二重和と等しい。
方針：直積の等号でない対の filter を使い、有限和を直積に沿って分解する。
規約：HA Proposition 1.3.1.10。使われ方：削除を二度適用する和と対合による相殺の接続。 -/
lemma sum_offDiag_eq {α : Type*} [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (K : Finset α) (f : α → α → M) :
    ∑ jk ∈ K.offDiag, f jk.1 jk.2 = ∑ j ∈ K, ∑ k ∈ K.erase j, f j k := by
  have h : K.offDiag = (K ×ˢ K).filter (fun jk => jk.1 ≠ jk.2) := by
    ext jk
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [h, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_erase]
  tauto

/-- 概要：内部点を一つずつ削除する二重和は、削除順の交換の符号で相殺する。
方針：二重和を相異なる点の組の和に戻し、既存の二重削除の対合を使う。
規約：HA Proposition 1.3.1.10。使われ方：実際の線形境界の二乗が零であること。 -/
lemma nested_double_erase {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I K : Finset α) (hKI : K ⊆ I) (f : Finset α → M) :
    ∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • ∑ k ∈ K.erase j,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) k • f ((I.erase j).erase k) = 0 := by
  simp only [Finset.smul_sum]
  rw [← sum_offDiag_eq]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sum_double_erase I K hKI f

end Index

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

namespace SimplexData

/-- 概要：正しい端点・次数・濃度のとき元の斉次成分を返し、それ以外は零とする補助評価。
方針：従来の `hom` の証明引数を条件分岐で供給する。
規約：HA Construction 1.3.1.6。使われ方：同じ次数の二重削除項を全域関数として扱う。
この補助評価は単体の表現や方程式を置き換えない。 -/
def homOrZero {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) : GradedHom A (s.obj a) (s.obj b) k :=
  if hI : 2 ≤ I.card then
    if ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) then
      if hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) then
        if hk : k = 2 - (I.card : ℤ) then s.hom I a b k hI ha hb hk else 0
      else 0
    else 0
  else 0

/-- 概要：適切な添字では全域化した評価は元の斉次成分に等しい。
方針：四つの条件分岐を全て正しい側で評価する。
規約：HA Construction 1.3.1.6。使われ方：線形境界と元の右辺の接続。 -/
lemma homOrZero_eq {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    s.homOrZero I a b k = s.hom I a b k hI ha hb hk := by
  simp only [homOrZero, dite_eq_left hI, dite_eq_left ha, dite_eq_left hb, dite_eq_left hk]

/-- 概要：単体の方程式の線形部分は、内部点を削除した成分の符号付き和。
方針：全域化した斉次成分を使い、端点と次数の証明なしに有限和を定義する。
規約：HA Construction 1.3.1.6。使われ方：残差の有限和の線形部分。 -/
def linearBoundary {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) : GradedHom A (s.obj a) (s.obj b) (k + 1) :=
  ∑ j ∈ Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • s.homOrZero (I.erase j) a b (k + 1)

/-- 概要：実際の斉次成分の削除部分を二度展開した符号付き和は零。
方針：内部点集合と削除の交換により同じ内部点集合の二重和にし、削除順の対合で相殺する。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式の二重削除項の消去。 -/
lemma linearBoundary_squared {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) :
    ∑ j ∈ Index.interior I a b,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • s.linearBoundary (I.erase j) a b (k + 1) = 0 := by
  simp only [linearBoundary, Index.interior_erase]
  exact Index.nested_double_erase I (Index.interior I a b) (Finset.filter_subset _ _)
    (fun J => s.homOrZero J a b (k + 1 + 1))

end SimplexData

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
