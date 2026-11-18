module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
# 置換の部分合成

概要：Berger–Fresse §0.10、§1.1.3 の shuffle 合成に使う置換の部分合成を構成する。
方針：挿入区間の内側の置換と、外側の置換による区間の移動を合成する。
規約：置換は右正則作用を持つ座標で表し、原典の単語による表示とは逆置換で対応する。
使われ方：Barratt–Eccles の各 shuffle 項の置換列の頂点を合成する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：外側の単位置換は挿入後も単位置換に延長される（Berger–Fresse §0.10）。
方針：入力の和分解の各成分で恒等写像を計算する。
規約：arity 0 の挿入を含む。
使われ方：置換の部分合成の単位則を証明する。 -/
@[simp] lemma outerPermutation_one (m n : ℕ) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i 1 = 1 := by
  apply Equiv.ext
  intro x
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).injective
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i) ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i).symm
      ((Equiv.sumCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadRemainingEquiv m i 1) (Equiv.refl _))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i x))) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i x
  erw [Equiv.apply_symm_apply]
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i x with j | j <;> rfl

/-- 概要：外側置換の積は挿入位置の移動を伴って合成される（Berger–Fresse §0.10）。
方針：挿入分解の二つの成分で残りの入力の置換を合成する。
規約：先に ρ、次に σ を適用する。
使われ方：置換の部分合成の外側等変性を導く。 -/
lemma outerPermutation_mul (m n : ℕ) (i : Fin (m + 1))
    (σ ρ : Equiv.Perm (Fin (m + 1))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i (σ * ρ) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n (ρ i) σ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ := by
  ext x
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation, Equiv.Perm.mul_def, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n i x with j | j <;> rfl

/-- 概要：置換 σ の入力 i へ置換 τ を代入する（Berger–Fresse §0.10、§1.1.3）。
方針：内側の入力を τ で動かしてから外側 σ に従って挿入区間を移す。
規約：結果の arity は m+n、外側の arity は m+1。
使われ方：Barratt–Eccles 合成の各頂点の置換となる。 -/
def permutationComposition (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ

/-- 概要：内側の置換への右乗法は挿入区間の右作用に一致する（Berger–Fresse §0.10）。
方針：内側置換の拡張が積を保つことを使う。
規約：右作用の座標なので積の順序を保つ。
使われ方：Barratt–Eccles 合成の内側等変性を与える。 -/
lemma permutationComposition_inner (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ κ : Equiv.Perm (Fin n)) :
    permutationComposition m n i σ (τ * κ) =
      permutationComposition m n i σ τ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ := by
  rw [permutationComposition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_mul, ← mul_assoc]
  rfl

/-- 概要：外側の置換への右乗法は挿入位置の移動と外側右作用に一致する（Berger–Fresse §0.10）。
方針：外側置換の積の法則と、内側置換が区間の移動と可換する等式を使う。
規約：ρ によって入力 i は ρ(i) へ移る。
使われ方：Barratt–Eccles 合成の外側等変性を与える。 -/
lemma permutationComposition_outer (m n : ℕ) (i : Fin (m + 1))
    (σ ρ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) :
    permutationComposition m n i (σ * ρ) τ =
      permutationComposition m n (ρ i) σ τ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_outer m n i ρ τ
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n (ρ i) τ * _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ at h
  rw [permutationComposition, outerPermutation_mul, mul_assoc, h, ← mul_assoc]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
