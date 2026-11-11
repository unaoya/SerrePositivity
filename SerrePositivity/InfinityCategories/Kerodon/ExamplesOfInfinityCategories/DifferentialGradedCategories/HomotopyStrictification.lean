module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationHomotopy

/-!
# m 次ホモトピーの低次数での厳密化

概要：m 次ホモトピーの始点の射を、終点と次数 ≤m で一致する射へ全次数ホモトピーで移す。
方針：入力の区間写像の実両端を a₀,a₁ とし、f−a₀+a₁ を作る。
規約：KST Construction A.5 の右辺の augmentation 補正。非被約な単体的整数加群の加減法。
使われ方：正規化後に (f−e)⊗(g−e) の二つの低次数消滅を使う前の準備。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial
variable {X : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g : linearizedSpace X ⟶ D} {m : ℕ}

/-- 概要：m 次ホモトピーの始点を低次数で終点と一致する射に置き換える。
方針：f−a₀+a₁ を取り、a₀,a₁ は入力の区間写像の実両端。
規約：KST Construction A.5 の非被約模型。使われ方：正規化へ送る前の写像。 -/
def LinearizedMHomotopy.strictifiedMap (H : LinearizedMHomotopy f g m) : linearizedSpace X ⟶ D :=
  f - linearizedEndpoint₀ X ≫ H.h + linearizedEndpoint₁ X ≫ H.h

/-- 概要：置き換えた射は次数 ≤m で終点の射に厳密に一致する。
方針：m 次ホモトピーの二つの両端条件を代入する。
規約：KST Construction A.5、零次を含む。使われ方：差の低次数消滅。 -/
lemma LinearizedMHomotopy.strictifiedMap_eq_low (H : LinearizedMHomotopy f g m)
    (n : ℕ) (hn : n ≤ m) : H.strictifiedMap.app (op ⦋n⦌) = g.app (op ⦋n⦌) := by
  simp only [LinearizedMHomotopy.strictifiedMap, NatTrans.app_add, NatTrans.app_sub,
    H.h₀ n hn, H.h₁ n hn, sub_self, zero_add]

/-- 概要：厳密化した射と終点の差は次数 ≤m で零。
方針：低次数の一致を差に適用する。
規約：KST Construction A.5 の右辺の augmentation 補正。
使われ方：正規化後のテンソルの次数評価。 -/
lemma LinearizedMHomotopy.strictifiedDifference_eq_zero (H : LinearizedMHomotopy f g m)
    (n : ℕ) (hn : n ≤ m) : (H.strictifiedMap - g).app (op ⦋n⦌) = 0 := by
  rw [NatTrans.app_sub, H.strictifiedMap_eq_low n hn, sub_self]

/-- 概要：厳密化した射は元の始点の射に全次数でホモトピック。
方針：f−a₀ の定数区間写像に入力の区間写像を加える。
規約：KST Construction A.5。入力に依存する標準的な線形構成で、被約複体に移さない。
使われ方：厳密化した二つの差のテンソルの計算を元の射へ戻す。 -/
def LinearizedMHomotopy.strictificationHomotopy (H : LinearizedMHomotopy f g m) :
    LinearizedHomotopy f H.strictifiedMap where
  h := linearizedCylinderProjection X ≫ (f - linearizedEndpoint₀ X ≫ H.h) + H.h
  h₀ := by
    rw [Preadditive.comp_add, linearizedEndpoint₀_projection_assoc]
    abel
  h₁ := by
    rw [Preadditive.comp_add, linearizedEndpoint₁_projection_assoc]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
