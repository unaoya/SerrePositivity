module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeSumFlags

/-!
# 二つの座標区間を保つ置換と符号付き和

概要：各区間内の置換の組を全座標の置換へ移し、その符号と旗の評価の二重和を計算する。
方針：和の置換を Fin の和の同値で移送し、符号の積と dg 合成の双加法性を使う。
規約：区間そのものの交換は行わず、先頭が後の射、末尾が前の射。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0） の残る旗の符号付き和を dg 合成にまとめる。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：先頭・末尾の各区間内の置換を全座標の置換へ上げる。
方針：和の置換を Fin(p+q) へ移送する。
規約：どの座標がどちらの区間に属するかを保つ。
使われ方：Kerodon 2.5.8（Tag 00S0） の順序に適合した全ての旗の添字。 -/
def cubeBlockPermutation {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    Equiv.Perm (Fin (p + q)) := finSumFinEquiv.permCongr (Equiv.Perm.sumCongr σ τ)

/-- 概要：先頭区間の座標は先頭区間の置換だけで動く。
方針：Fin の和の左側で移送を評価する。
規約：末尾座標数 q を castAdd に明示する。
使われ方：HA 1.3.1.16 の置換した接頭の旗の計算。 -/
lemma cubeBlockPermutation_castAdd {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) (j : Fin p) :
    cubeBlockPermutation σ τ (Fin.castAdd q j) = Fin.castAdd q (σ j) := by
  simp [cubeBlockPermutation, Equiv.permCongr_apply]

/-- 概要：末尾区間の座標は末尾区間の置換だけで動く。
方針：Fin の和の右側で移送を評価する。
規約：先頭座標数 p を natAdd に明示する。
使われ方：HA 1.3.1.16 の置換した接尾の旗の計算。 -/
lemma cubeBlockPermutation_natAdd {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) (j : Fin q) :
    cubeBlockPermutation σ τ (Fin.natAdd p j) = Fin.natAdd p (τ j) := by
  simp [cubeBlockPermutation, Equiv.permCongr_apply]

/-- 概要：区間を保つ置換の符号は二つの置換の符号の積である。
方針：同値による符号の不変性と和の置換の符号の式を使う。
規約：整数の係数として述べる。
使われ方：Kerodon 2.5.8（Tag 00S0） の二つの旗の符号付き和の積。 -/
lemma cubeBlockPermutation_sign {p q : ℕ} (σ : Equiv.Perm (Fin p))
    (τ : Equiv.Perm (Fin q)) :
    (Equiv.Perm.sign (cubeBlockPermutation σ τ) : ℤ) =
      (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) := by
  simp [cubeBlockPermutation, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

/-- 概要：連結した番号付けの区間内置換は各番号付けを置換してから連結する操作に等しい。
方針：Fin の和の左右で同値の値を比較する。
規約：置換の合成は座標番号から座標への順に trans で書く。
使われ方：HA 1.3.1.16 の残る旗を二つの置換で番号付けする。 -/
lemma cubeBlockPermutation_trans_enumeration {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B) (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    (cubeBlockPermutation σ τ).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration e f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration (σ.trans e) (τ.trans f) := by
  ext j
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  cases t <;> simp [cubeBlockPermutation, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeSumEnumeration, Equiv.permCongr_apply]

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y z : D}

/-- 概要：区間を保つ置換の符号付き評価の合成の二重和は二つの立方体評価の合成である。
方針：置換の符号を積に分け、dg 合成の各変数の和と整数符号の保存を使う。
規約：零次元の因子も含む。対象の次数は −(p+q)。
使われ方：Kerodon 2.5.8（Tag 00S0） の残る全旗の和を通常順の dg 合成へまとめる。 -/
lemma cubeBlockPermutation_signed_sum {A B : Type u} {p q : ℕ}
    (e : Fin p ≃ A) (f : Fin q ≃ B)
    (ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z)
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) :
    (∑ σ : Equiv.Perm (Fin p), ∑ τ : Equiv.Perm (Fin q),
      (Equiv.Perm.sign (cubeBlockPermutation σ τ) : ℤ) •
        compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (σ.trans e) ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (τ.trans f) φ)
          (show -(q : ℤ) + -(p : ℤ) = -((p + q : ℕ) : ℤ) by push_cast; omega)) =
      compose R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation f φ) (by push_cast; omega) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  rw [cubeBlockPermutation_sign, mul_smul]
  symm
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left (Equiv.Perm.sign σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (σ.trans e) ψ)
    ((Equiv.Perm.sign τ : ℤ) • _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (τ.trans f) φ)
    (show -(q : ℤ) + -(p : ℤ) = -((p + q : ℕ) : ℤ) by push_cast; omega)
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right (Equiv.Perm.sign τ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (σ.trans e) ψ) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeFlagEvaluation (τ.trans f) φ)
    (show -(q : ℤ) + -(p : ℤ) = -((p + q : ℕ) : ℤ) by push_cast; omega)
  simp only [Units.smul_def] at h₁ h₂
  exact h₁.trans (congrArg (fun t ↦ (Equiv.Perm.sign σ : ℤ) • t) h₂)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
