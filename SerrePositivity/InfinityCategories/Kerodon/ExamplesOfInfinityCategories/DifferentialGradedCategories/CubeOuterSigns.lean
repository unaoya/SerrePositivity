module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubePermutationFaces

/-!
# 最大旗の外側の面の符号と添字

概要：最初または最後の座標を固定する分解で、置換符号と単体境界符号を計算する。
方針：先頭分解と巡回置換の符号を使う。
規約：最後の面の境界係数を含めると座標0面に負号が付く。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の立方体境界の符号。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：末尾座標と残りの置換は全置換と同値である。
方針：先頭座標の分解に巡回置換の右乗法を合成する。
規約：逆写像ではなく、この同値の順方向が末尾指定の置換を作る。
使われ方：Kerodon 2.5.9（Tag 00SC） の最後の面の和の添字の交換。 -/
def cubeLastPermutationEquiv {n : ℕ} :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃ Equiv.Perm (Fin (n + 2)) :=
  Equiv.Perm.decomposeFin'.symm.trans (Equiv.mulRight (finRotate (n + 2)))

/-- 概要：末尾分解の同値を指定した点と置換に評価すると末尾指定の置換になる。
方針：同値と置換の積の定義を評価する。
規約：右乗法は位置の巡回移動である。
使われ方：Kerodon 2.5.9（Tag 00SC） の最後の面の和の計算。 -/
lemma cubeLastPermutationEquiv_apply {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) : cubeLastPermutationEquiv (i, σ) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutation i σ :=
  rfl

/-- 概要：最初の座標 i を固定した置換の符号は (−1)^i と残りの置換の符号の積。
方針：Mathlib の先頭分解の符号を整数に移す。
規約：以後の和の係数として整数で述べる。
使われ方：HA 1.3.1.16 の座標1面の符号。 -/
lemma cubeFirstPermutation_sign {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (Equiv.Perm.decomposeFin'Symm i σ) : ℤ) =
      (-1 : ℤ) ^ i.val * (Equiv.Perm.sign σ : ℤ) := by
  rw [Equiv.Perm.sign_decomposeFin'Symm]
  simp

/-- 概要：末尾を固定した置換の符号には巡回移動の (−1)^(n+1) が掛かる。
方針：先頭分解と巡回置換の符号の乗法性を使う。
規約：置換の型は Fin (n+2)。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標0面の符号の準備。 -/
lemma cubeLastPermutation_sign {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutation i σ) : ℤ) =
      (-1 : ℤ) ^ (n + 1) * ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign σ : ℤ)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutation
  rw [Equiv.Perm.sign_trans]
  simp only [Units.val_mul, cubeFirstPermutation_sign, sign_finRotate,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  have he : n + 2 - 1 = n + 1 := by omega
  rw [he]
  ring

/-- 概要：最後の面の単体境界係数を掛けると座標0面の係数は −(−1)^i となる。
方針：巡回移動の符号と最後の面の符号を掛け合わせる。
規約：整数の係数の等式である。
使われ方：HA 1.3.1.16 の座標1面−座標0面の境界公式。 -/
lemma cubeLastBoundary_sign {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (-1 : ℤ) ^ (n + 2) * (Equiv.Perm.sign (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeLastPermutation i σ) : ℤ) =
      -((-1 : ℤ) ^ i.val * (Equiv.Perm.sign σ : ℤ)) := by
  rw [cubeLastPermutation_sign]
  have hs : (-1 : ℤ) ^ (n + 2) * (-1 : ℤ) ^ (n + 1) = -1 := by
    rw [← pow_add]
    have he : n + 2 + (n + 1) = 2 * (n + 1) + 1 := by omega
    rw [he, pow_add, pow_mul]
    norm_num
  calc
    _ = ((-1 : ℤ) ^ (n + 2) * (-1 : ℤ) ^ (n + 1)) *
        ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign σ : ℤ)) := by ring
    _ = _ := by rw [hs, neg_one_mul]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
