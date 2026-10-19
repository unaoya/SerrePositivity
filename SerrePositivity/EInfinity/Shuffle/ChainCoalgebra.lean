module

public import SerrePositivity.EInfinity.Shuffle.CoalgebraComponents
public import SerrePositivity.EInfinity.Shuffle.ChainNaturality
public import SerrePositivity.EInfinity.AlexanderWhitney.FiniteCuts
public import SerrePositivity.EInfinity.NatTensor.InterchangeComponents

/-!
# 一般 shuffle 鎖写像の AW 余代数適合性

概要：Berger–Fresse §1.1.4 の余代数射性を実際の鎖写像の等式として証明する。
方針：二つの AW 対角を切断座標の有限和で展開し、四因子交換の符号公式を用いる。
規約：余代数のテンソルの中間二因子を Koszul 符号つきで交換する。
使われ方：Barratt–Eccles の部分合成と Hopf 対角の可換性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Shuffle

open CategoryTheory MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：一般 shuffle 鎖写像は AW 余積を保つ（BF §1.1.4）。
方針：斉次包含で検査し、二つの切断座標の有限和の各項を比較する。
規約：任意の可換係数環と任意の小さい単体集合に成立する。
使われ方：E の部分合成が余代数射であることを導く。 -/
lemma chainMap_diagonal (X Y : SSet.{0}) :
    chainMap A X Y ≫ AlexanderWhitney.diagonal A (X ⊗ Y) =
      HomologicalComplex.tensorHom (AlexanderWhitney.diagonal A X)
          (AlexanderWhitney.diagonal A Y) ≫
        (NatTensor.interchange (AlexanderWhitney.chains A X) (AlexanderWhitney.chains A X)
          (AlexanderWhitney.chains A Y) (AlexanderWhitney.chains A Y)).hom ≫
        HomologicalComplex.tensorHom (chainMap A X Y) (chainMap A X Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  subst n
  simp only [HomologicalComplex.comp_f]
  rw [ι_chainMap_assoc, component_diagonal, tensorHom_inclusion_assoc]
  simp only [AlexanderWhitney.diagonal_f_eq_sum_cuts, sum_tensor, tensor_sum,
    Preadditive.sum_comp]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  rw [NatTensor.inclusion_interchange_assoc]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  rw [NatTensor.inclusion_tensorMap]
  simp only [tensorHom_comp_tensorHom_assoc, ι_chainMap]
  rw [Nat.mul_comm t.val (p - r.val)]

end SerrePositivity.EInfinity.Shuffle
