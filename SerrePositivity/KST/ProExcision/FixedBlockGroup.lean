module
public import SerrePositivity.KST.ProExcision.BlockColumnGroup

/-!
# 補助列を固定する非可換な実ブロック群

概要：first n 列と一つの補助行を固定する行列単位の部分群を構成する。
方針：積と逆が列・行の固定性を保つことを行列積から証明する。
規約：KST Lemma 4.16 の P のブロック埋め込みを含む周囲の実部分群。
使われ方：ψ(Q) との可換性と μ の実準同型。T_{n,m−1}(I) 自体との同一視は別工程。
-/
@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]
variable {ι : Type v} {κ : Type w} [Fintype κ] [DecidableEq κ]

/-- 概要：右因子の固定列は左因子を掛けても同じ列を与える。
方針：固定列を恒等行列の列に置き換える。
規約：KST Lemma 4.16 のブロックの積。
使われ方：固定列を持つ行列単位の部分群の閉性。 -/
lemma matrix_mul_fixed_column (M N : Matrix κ κ R) (j : κ)
    (hN : ∀ i, N i j = (1 : Matrix κ κ R) i j) : ∀ i, (M * N) i j = M i j := by
  intro i
  calc
    _ = (M * (1 : Matrix κ κ R)) i j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [hN k]
    _ = _ := by rw [mul_one]

/-- 概要：左因子の固定行は右因子を掛けても同じ行を与える。
方針：固定行を恒等行列の行に置き換える。
規約：KST Lemma 4.16 のブロックの積。
使われ方：固定行を持つ行列単位の部分群の閉性。 -/
lemma matrix_mul_fixed_row (M N : Matrix κ κ R) (i : κ)
    (hM : ∀ j, M i j = (1 : Matrix κ κ R) i j) : ∀ j, (M * N) i j = N i j := by
  intro j
  calc
    _ = ((1 : Matrix κ κ R) * N) i j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [hM k]
    _ = _ := by rw [one_mul]

/-- 概要：指定した全ての列と補助行を固定する行列単位の部分群。
方針：積の固定性と逆元を掛けた恒等式から逆の固定性を証明する。
規約：KST 4.16 の P を埋め込む周囲群。三角性や係数イデアルはまだ指定しない。
使われ方：実 μ の準同型性を、可換性の仮定の追加なしに導く。 -/
def fixedBlockSubgroup (r : ι → κ) (p : κ) : Subgroup (Matrix κ κ R)ˣ where
  carrier := {M | (∀ k i, (M : Matrix κ κ R) i (r k) = (1 : Matrix κ κ R) i (r k)) ∧
    ∀ j, (M : Matrix κ κ R) p j = (1 : Matrix κ κ R) p j}
  one_mem' := ⟨by intros; rfl, by intros; rfl⟩
  mul_mem' := by
    intro M N hM hN
    constructor
    · intro k i
      exact (matrix_mul_fixed_column (M : Matrix κ κ R) (N : Matrix κ κ R) (r k) (hN.1 k) i).trans
        (hM.1 k i)
    · intro j
      exact (matrix_mul_fixed_row (M : Matrix κ κ R) (N : Matrix κ κ R) p hM.2 j).trans (hN.2 j)
  inv_mem' := by
    intro M hM
    constructor
    · intro k i
      have h := matrix_mul_fixed_column (↑M⁻¹ : Matrix κ κ R) (↑M : Matrix κ κ R) (r k) (hM.1 k) i
      have hid : (↑M⁻¹ : Matrix κ κ R) * (↑M : Matrix κ κ R) = 1 := M.inv_val
      rw [hid] at h
      exact h.symm
    · intro j
      have h := matrix_mul_fixed_row (↑M : Matrix κ κ R) (↑M⁻¹ : Matrix κ κ R) p hM.2 j
      have hid : (↑M : Matrix κ κ R) * (↑M⁻¹ : Matrix κ κ R) = 1 := M.val_inv
      rw [hid] at h
      exact h.symm

/-- 概要：固定ブロック部分群の全体と補助列の群の像は可換。
方針：部分群の固定列・固定行の条件を実行列の可換性に適用する。
規約：KST 4.16、I の可換性を要しない P,Q の像の可換性。
使われ方：直積準同型 μ の構成。 -/
lemma fixedBlockSubgroup_commute_column [Fintype ι] (r : ι → κ) (p : κ)
    (hp : ∀ i, p ≠ r i) (M : fixedBlockSubgroup (R := R) r p) (v : Multiplicative (ι → R)) :
    Commute (M : (Matrix κ κ R)ˣ) (blockColumnHom r p hp v) := by
  apply Units.ext
  exact (matrix_commute_one_add_blockColumn (M : (Matrix κ κ R)ˣ) r p v.toAdd M.property.1 M.property.2).eq

/-- 概要：固定ブロック群と補助列群からの積の準同型 μ。
方針：実行列で証明した可換性を用い、二つの因子の実準同型を掛ける。
規約：KST A.5 の μ 版、Lemma 4.16 のブロック埋め込みの周囲群。
使われ方：三角ブロック群の埋め込みに制限して P×Q→H を得る。 -/
def fixedBlockProduct [Fintype ι] (r : ι → κ) (p : κ) (hp : ∀ i, p ≠ r i) :
    fixedBlockSubgroup (R := R) r p × Multiplicative (ι → R) →* (Matrix κ κ R)ˣ :=
  commutingProductHom (fixedBlockSubgroup (R := R) r p).subtype (blockColumnHom r p hp)
    (fixedBlockSubgroup_commute_column r p hp)

end SerrePositivity.KST.ProExcision
