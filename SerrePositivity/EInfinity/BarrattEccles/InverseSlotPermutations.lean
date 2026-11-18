module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationComposition

/-!
# 挿入区間の置換と逆元

概要：Berger–Fresse §0.10 の区間の置換の逆元を計算する。
方針：内側と外側の置換の積の公式に逆置換を適用する。
規約：外側の逆置換では挿入位置も移す。
使われ方：右作用による等変性を対称列の逆置換の規約へ合わせる。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：内側の置換の拡張は逆元を保つ（Berger–Fresse §0.10）。
方針：積と単位の保存を使う。
規約：挿入位置は固定する。
使われ方：対称列の内側等変性を右作用の公式から得る。 -/
lemma innerPermutation_inv (m n : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i σ⁻¹ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i σ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_mul, inv_mul_cancel, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_one]

/-- 概要：外側の逆置換は移した挿入位置で元の拡張の逆となる（Berger–Fresse §0.10）。
方針：位置の移動を伴う積の公式を逆置換と元の置換へ適用する。
規約：逆置換の挿入位置は σ(i) である。
使われ方：対称列の外側等変性を右作用の公式から得る。 -/
lemma outerPermutation_inv (m n : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n (σ i) σ⁻¹ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← outerPermutation_mul, inv_mul_cancel, outerPermutation_one]

end SerrePositivity.EInfinity.BarrattEccles
