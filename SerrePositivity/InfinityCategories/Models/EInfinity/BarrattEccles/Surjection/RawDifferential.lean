module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentDeletionSigns
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentDeletions

/-!
模型。文献の定義との比較は後で
# 任意の語の削除和と正規化の両立

概要：Berger–Fresse §1.2.3・§1.4.4 の削除和を退化・非全射な語も含めて扱う。
方針：隣接同値の削除の二項を相殺し、それ以外の項は退化として零にする。
規約：次数 d+1 から d へ移すが、平方零はここで仮定も主張もしない。
使われ方：table の出力を正規化する前の有限和で微分保存を計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：任意の有限語の符号付き削除和（BF §1.2.3）。
方針：全位置の削除を整数係数で加算し、各出力を生成元か零へ正規化する。
規約：入力語に全射性・非退化性を要求しない。
使われ方：TR の行長の和から微分を項ごとに計算する。 -/
def rawDifferential {n d : ℕ} (v : Fin (n + (d + 1)) → Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A n d :=
  ∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient v i • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase v i)

/-- 概要：非全射な語の削除和は零（BF §1.2.3）。
方針：全ての削除後の語が非全射のままなので各項が零。
規約：隣接重複の有無によらない。
使われ方：正規化との両立の非全射の分岐を処理する。 -/
lemma rawDifferential_eq_zero_of_not_surjective {n d : ℕ}
    (v : Fin (n + (d + 1)) → Fin n) (hv : ¬ Function.Surjective v) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_surjective _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_surjective_erase v hv i), smul_zero]

/-- 概要：隣接同値を持つ語の削除和は零（BF §1.4.4）。
方針：その二位置の削除は同じ語で逆符号、残りは隣接重複を保つ。
規約：基礎環の標数の仮定は不要。
使われ方：退化語の境界の正規化を計算する。 -/
lemma rawDifferential_eq_zero_of_adjacent_eq {n d : ℕ}
    (v : Fin (n + (d + 1)) → Fin n) (i j : Fin (n + (d + 1)))
    (hij : i.val + 1 = j.val) (he : v i = v j) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v = 0 := by
  have hne : i ≠ j := by
    intro h
    have hv := congrArg (fun k : Fin (n + (d + 1)) => k.val) h
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential, Finset.sum_eq_add i j hne]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_adjacent_eq v i j hij he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_adjacent_eq v i j hij he,
      neg_zsmul, add_neg_cancel]
  · intro k _ hk
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_nondegenerate _ _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_not_nondegenerate_of_adjacent_eq v i j k hij he hk.1 hk.2), smul_zero]
  · simp
  · simp

/-- 概要：任意の退化語の削除和は零（BF §1.4.4）。
方針：非退化条件の否定から隣接同値を取り出す。
規約：非全射な退化語も含む。
使われ方：既存の自由加群の微分と全語の削除和を同定する。 -/
lemma rawDifferential_eq_zero_of_not_nondegenerate {n d : ℕ}
    (v : Fin (n + (d + 1)) → Fin n) (hv : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v = 0 := by
  classical
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate at hv
  obtain ⟨i, hi⟩ := not_forall.mp hv
  obtain ⟨j, hj⟩ := not_forall.mp hi
  obtain ⟨hij, hne⟩ := not_imp.mp hj
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential_eq_zero_of_adjacent_eq A v i j hij (not_ne_iff.mp hne)

/-- 概要：生成元か零への正規化は削除微分と可換（BF §1.4.4）。
方針：基底語では定義、退化・非全射語では削除和と生成元の両方が零。
規約：入力語は任意。
使われ方：TR の全ての table 出力の境界を同じ有限和の式で計算する。 -/
lemma differential_generator {n d : ℕ} (v : Fin (n + (d + 1)) → Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential A v := by
  by_cases hs : Function.Surjective v
  · by_cases hn : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate v
    · rw [show _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n (d + 1) (ULift.up ⟨v, hs, hn⟩) from
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word A ⟨v, hs, hn⟩, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential_basis]
      rfl
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_nondegenerate A v hn, map_zero,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential_eq_zero_of_not_nondegenerate A v hn]
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_eq_zero_of_not_surjective A v hs, map_zero,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rawDifferential_eq_zero_of_not_surjective A v hs]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
