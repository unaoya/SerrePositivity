module
public import SerrePositivity.KST.ProExcision.FixedBlockGroup
public import Mathlib.RingTheory.NonUnitalSubring.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.BigOperators

/-!
# 非可換な三角ブロック行列の係数模型

概要：first n 列を零にした狭義上三角行列を、両側イデアル内の係数とともに部分環へ束ねる。
方針：許される成分の関係の推移性と両側イデアルの有限和・積の吸収を使う。
規約：KST Lemma 4.16 の T_{n,m}(I) の非単位部分の実模型。
使われ方：1+A とその逆の非自明成分がこの部分環にある行列単位の部分群。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：係数イデアル内の狭義上三角行列で first n 列が零となる部分環。
方針：行列積の各項で許される二つの成分の推移性を使う。
規約：KST Lemma 4.16、I の可換性は不要。
使われ方：T_{n,m}(I) の実行列の係数と三角性の指定。 -/
def blockPatternSubring (N n : ℕ) (J : TwoSidedIdeal R) : NonUnitalSubring (Matrix (Fin N) (Fin N) R) where
  carrier := {A | (∀ i j, ¬ (i < j ∧ n ≤ j.val) → A i j = 0) ∧ ∀ i j, A i j ∈ J}
  zero_mem' := by
    constructor
    · intros; rfl
    · intros; exact J.zero_mem
  add_mem' := by
    intro A B hA hB
    constructor
    · intro i j hij
      change A i j + B i j = 0
      rw [hA.1 i j hij, hB.1 i j hij, add_zero]
    · intro i j
      exact J.add_mem (hA.2 i j) (hB.2 i j)
  neg_mem' := by
    intro A hA
    constructor
    · intro i j hij
      change - A i j = 0
      rw [hA.1 i j hij, neg_zero]
    · intro i j
      exact J.neg_mem (hA.2 i j)
  mul_mem' := by
    intro A B hA hB
    constructor
    · intro i j hij
      change ∑ k, A i k * B k j = 0
      apply Finset.sum_eq_zero
      intro k _
      by_cases hik : i < k ∧ n ≤ k.val
      · have hkj : ¬ (k < j ∧ n ≤ j.val) := by
          intro hkj
          exact hij ⟨lt_trans hik.1 hkj.1, hkj.2⟩
        rw [hB.1 k j hkj, mul_zero]
      · rw [hA.1 i k hik, zero_mul]
    · intro i j
      change ∑ k, A i k * B k j ∈ J
      exact J.finsetSum_mem _ _ (fun k _ ↦ J.mul_mem_left _ _ (hB.2 k j))

/-- 概要：1 からの差が部分環に入る二つの元は積でも同じ条件を満たす。
方針：ab−1=(a−1)+(b−1)+(a−1)(b−1) を非可換に展開する。
規約：KST 4.16、非単位部分環の乗法の閉性。
使われ方：行列単位の三角ブロック部分群の積の閉性。 -/
lemma oneDifference_mul_mem (S : NonUnitalSubring R) (a b : R)
    (ha : a - 1 ∈ S) (hb : b - 1 ∈ S) : a * b - 1 ∈ S := by
  have h : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by noncomm_ring
  rw [h]
  exact S.add_mem (S.add_mem ha hb) (S.mul_mem ha hb)

/-- 概要：単位と逆の 1 からの差が非単位部分環に入る単位の部分群。
方針：積について差の積公式を使い、逆について二条件を交換する。
規約：KST 4.16 の実行列群。逆の条件も明示して定義する。
使われ方：三角ブロックの係数模型を実際の群にする。 -/
def oneDifferenceSubgroup (S : NonUnitalSubring R) : Subgroup Rˣ where
  carrier := {a | (a : R) - 1 ∈ S ∧ ((a⁻¹ : Rˣ) : R) - 1 ∈ S}
  one_mem' := by
    constructor <;> simpa only [Units.val_one, inv_one, sub_self] using S.zero_mem
  mul_mem' := by
    intro a b ha hb
    constructor
    · exact oneDifference_mul_mem S (a : R) (b : R) ha.1 hb.1
    · change ((b⁻¹ : Rˣ) : R) * ((a⁻¹ : Rˣ) : R) - 1 ∈ S
      exact oneDifference_mul_mem S _ _ hb.2 ha.2
  inv_mem' := by
    intro a ha
    constructor
    · exact ha.2
    · simpa only [inv_inv] using ha.1

/-- 概要：両側イデアル内の係数を持つ実三角ブロック群。
方針：first n 列が零となる狭義三角部分環から単位の部分群を作る。
規約：KST Lemma 4.16 の T_{n,m}(I) の実模型、周囲の単位環は別に指定する。
使われ方：I を単位化の核イデアルとした場合の非可換な P,H の構成。 -/
def triangularBlockGroup (n m : ℕ) (J : TwoSidedIdeal R) : Subgroup (Matrix (Fin (n + m)) (Fin (n + m)) R)ˣ :=
  oneDifferenceSubgroup (blockPatternSubring (n + m) n J)

/-- 概要：三角ブロック群の first n 列は恒等行列の列。
方針：1 からの差の許されない成分が零であることを使う。
規約：KST Lemma 4.16 の P の固定列。
使われ方：補助列との可換性に必要な行列成分の条件。 -/
lemma triangularBlockGroup_fixed_column (n m : ℕ) (J : TwoSidedIdeal R)
    (M : triangularBlockGroup n m J) (j : Fin (n + m)) (hj : j.val < n) (i : Fin (n + m)) :
    (M : (Matrix (Fin (n + m)) (Fin (n + m)) R)ˣ).val i j =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j := by
  have h : ¬ (i < j ∧ n ≤ j.val) := by omega
  have hz := M.property.1.1 i j h
  change (M : (Matrix (Fin (n + m)) (Fin (n + m)) R)ˣ).val i j -
    (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j = 0 at hz
  exact sub_eq_zero.mp hz

/-- 概要：三角ブロック群の最後の行は恒等行列の行。
方針：最後の行から出る狭義三角成分が無いことを使う。
規約：KST 4.16 の補助元の行の固定性。
使われ方：追加座標を挿入する前の実ブロック群の成分計算。 -/
lemma triangularBlockGroup_fixed_max_row (n m : ℕ) (J : TwoSidedIdeal R)
    (M : triangularBlockGroup n m J) (i : Fin (n + m)) (hi : ∀ j : Fin (n + m), j ≤ i)
    (j : Fin (n + m)) :
    (M : (Matrix (Fin (n + m)) (Fin (n + m)) R)ˣ).val i j =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j := by
  have h : ¬ (i < j ∧ n ≤ j.val) := by intro h; exact (not_lt_of_ge (hi j)) h.1
  have hz := M.property.1.1 i j h
  change (M : (Matrix (Fin (n + m)) (Fin (n + m)) R)ˣ).val i j -
    (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j = 0 at hz
  exact sub_eq_zero.mp hz

end SerrePositivity.KST.ProExcision
