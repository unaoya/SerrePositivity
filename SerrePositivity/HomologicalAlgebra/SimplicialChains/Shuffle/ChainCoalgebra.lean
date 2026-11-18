module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.CoalgebraComponents
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.ChainNaturality
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.FiniteCuts
public import SerrePositivity.HomologicalAlgebra.Complexes.NatTensor.InterchangeComponents

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

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：一般 shuffle 鎖写像は AW 余積を保つ（BF §1.1.4）。
方針：斉次包含で検査し、二つの切断座標の有限和の各項を比較する。
規約：任意の可換係数環と任意の小さい単体集合に成立する。
使われ方：E の部分合成が余代数射であることを導く。 -/
lemma chainMap_diagonal (X Y : SSet.{0}) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.chainMap A X Y ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A (X ⊗ Y) =
      HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A X)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A Y) ≫
        (_root_.SerrePositivity.NatTensor.interchange (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X)
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y)).hom ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap A X Y) (_root_.SerrePositivity.SimplicialChains.Shuffle.chainMap A X Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = n at h
  subst n
  simp only [HomologicalComplex.comp_f]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.ι_chainMap_assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.component_diagonal, _root_.SerrePositivity.SimplicialChains.Shuffle.tensorHom_inclusion_assoc]
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal_f_eq_sum_cuts, sum_tensor, tensor_sum,
    Preadditive.sum_comp]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  rw [_root_.SerrePositivity.NatTensor.inclusion_interchange_assoc]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
  rw [_root_.SerrePositivity.NatTensor.inclusion_tensorMap]
  simp only [tensorHom_comp_tensorHom_assoc, _root_.SerrePositivity.SimplicialChains.Shuffle.ι_chainMap]
  rw [Nat.mul_comm t.val (p - r.val)]

end SerrePositivity.SimplicialChains.Shuffle
