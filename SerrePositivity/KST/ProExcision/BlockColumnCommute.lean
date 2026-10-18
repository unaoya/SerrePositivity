module
public import SerrePositivity.KST.ProExcision.BlockColumn

/-!
# 非可換なブロック群の補助列との可換性

概要：first n 列で恒等、補助行でも恒等の行列は ψ の列と可換。
方針：単一成分行列の積を固定列・固定行の条件で評価する。
規約：KST Lemma 4.16 への μ 版 A.5 の適用。I の可換性は不要。
使われ方：P の埋め込みと ψ(Q) の像の可換性から μ の乗法保存を証明する。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]
variable {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- 概要：列 r が恒等行列の列なら単一成分行列への左積は恒等。
方針：非零になり得る列でだけ積を評価する。
規約：KST Lemma 4.16 の P の first n 列。
使われ方：P の埋め込みによる ψ の非自明な列の固定性。 -/
lemma matrix_mul_single_of_fixed_column (M : Matrix κ κ R) (r p : κ) (c : R)
    (hM : ∀ i, M i r = (1 : Matrix κ κ R) i r) :
    M * Matrix.single r p c = Matrix.single r p c := by
  calc
    _ = (1 : Matrix κ κ R) * Matrix.single r p c := by
      ext i j
      by_cases h : j = p
      · subst j
        simp only [Matrix.mul_single_apply_same, hM i]
      · rw [Matrix.mul_single_apply_of_ne c r p i j h M,
          Matrix.mul_single_apply_of_ne c r p i j h 1]
    _ = _ := one_mul _

/-- 概要：行 p が恒等行列の行なら単一成分行列への右積は恒等。
方針：非零になり得る行でだけ積を評価する。
規約：KST Lemma 4.16 の P の追加補助行。
使われ方：ψ(Q) による P の埋め込みとの逆順の積。 -/
lemma matrix_single_mul_of_fixed_row (M : Matrix κ κ R) (r p : κ) (c : R)
    (hM : ∀ j, M p j = (1 : Matrix κ κ R) p j) :
    Matrix.single r p c * M = Matrix.single r p c := by
  calc
    _ = Matrix.single r p c * (1 : Matrix κ κ R) := by
      ext i j
      by_cases h : i = r
      · subst i
        simp only [Matrix.single_mul_apply_same, hM j]
      · rw [Matrix.single_mul_apply_of_ne c r p i j h M,
          Matrix.single_mul_apply_of_ne c r p i j h 1]
    _ = _ := mul_one _

/-- 概要：P の固定列と補助固定行から補助列との可換性を得る。
方針：列の有限和の両側の積がともにその列自体になることを使う。
規約：KST Lemma 4.16 の μ の非可換再記述。
使われ方：P と ψ(Q) の全体の可換性、I の可換性を仮定しない。 -/
lemma matrix_commute_one_add_blockColumn (M : Matrix κ κ R) (r : ι → κ) (p : κ) (v : ι → R)
    (hcol : ∀ k i, M i (r k) = (1 : Matrix κ κ R) i (r k))
    (hrow : ∀ j, M p j = (1 : Matrix κ κ R) p j) :
    Commute M (1 + blockColumn r p v) := by
  have hl : M * blockColumn r p v = blockColumn r p v := by
    simp only [blockColumn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact matrix_mul_single_of_fixed_column M (r i) p (v i) (hcol i)
  have hr : blockColumn r p v * M = blockColumn r p v := by
    simp only [blockColumn, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact matrix_single_mul_of_fixed_row M (r i) p (v i) hrow
  change M * (1 + blockColumn r p v) = (1 + blockColumn r p v) * M
  rw [mul_add, add_mul, mul_one, one_mul, hl, hr]

end SerrePositivity.KST.ProExcision
