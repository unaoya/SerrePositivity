module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientProjections
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorResolutionComparison
public import SerrePositivity.EInfinity.BarrattEccles.Hopf
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.HopfComponents

/-!
# 二色の実際の係数比較射

## 概要
HA 3.2.4.7 の余積とテンソルの比較に現れる、二色の係数比較射を構成する。

## 方針
実際の Hopf 対角の後に両色への零入力代入を適用し、二色部分群の表現の射へ移す。

## 規約
射影解像度から任意の比較射を選び直さず、指定された Hopf 比較を順射にする。

## 使われ方
指定増大の可換性の確認後、解像度の比較から等変な鎖ホモトピー逆を得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level operad sequence
variable (A : Type u) [CommRing A]

/-- 実際の Hopf 対角と、二つの零入力への代入からなる指定係数射。 -/
def twoColorCoefficientComparison (m n : ℕ) :
    (operad A).arity (m + n) ⟶ (operad A).arity m ⊗ (operad A).arity n :=
  (hopf A).diagonalComponent (m + n) ≫
    (twoColorLeftCoefficient A m n ⊗ₘ twoColorRightCoefficient A m n)

/-- 指定係数射は、両色の置換を二つの出力因子の置換へ移す。 -/
lemma twoColorCoefficientComparison_equivariance (m n : ℕ)
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)) :
    (operad A).sequence.map
      (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ≫
        twoColorCoefficientComparison A m n = twoColorCoefficientComparison A m n ≫
          ((operad A).sequence.map (FiniteBijection.permutation m σ) ⊗ₘ
            (operad A).sequence.map (FiniteBijection.permutation n τ)) := by
  have hd : (operad A).sequence.map
      (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ≫
        (hopf A).diagonalComponent (m + n) = (hopf A).diagonalComponent (m + n) ≫
          ((operad A).sequence.map
            (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ)) ⊗ₘ
            (operad A).sequence.map
              (FiniteBijection.permutation (m + n) (FiniteBijection.blockEquiv σ τ))) :=
    (hopf A).diagonal.map.naturality _
  unfold twoColorCoefficientComparison
  rw [← Category.assoc, hd, Category.assoc, tensorHom_comp_tensorHom,
    twoColorLeftCoefficient_equivariance, twoColorRightCoefficient_equivariance,
    ← tensorHom_comp_tensorHom, Category.assoc]

/-- 始域の複体上の実際の二色部分群作用。 -/
def twoColorSourceComplexAction (m n : ℕ) :
    TwoColorGroup.{u} m n →* End (complex A (m + n)) :=
  (arityComplexAction A (m + n)).comp (twoColorPermutationHom.{u} m n).range.subtype

/-- 指定係数射の、実際の二色部分群作用に関する可換性。 -/
lemma twoColorCoefficientComparison_action (m n : ℕ) (g : TwoColorGroup.{u} m n) :
    (twoColorSourceComplexAction A m n g).asHom ≫ twoColorCoefficientComparison A m n =
      twoColorCoefficientComparison A m n ≫
        (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n) g).asHom := by
  have h := twoColorCoefficientComparison_equivariance A m n
    (twoColorLeftProjection m n g).down (twoColorRightProjection m n g).down
  change (sequence A).map _ ≫ twoColorCoefficientComparison A m n =
    twoColorCoefficientComparison A m n ≫ ((sequence A).map _ ⊗ₘ (sequence A).map _) at h
  rw [sequence_map_permutation, sequence_map_permutation, sequence_map_permutation] at h
  change complexRightAction A (m + n) g.val.down⁻¹ ≫ _ = _ ≫
    (complexRightAction A m (twoColorLeftProjection m n g).down⁻¹ ⊗ₘ
      complexRightAction A n (twoColorRightProjection m n g).down⁻¹)
  rw [twoColorGroup_block]
  exact h

/-- 実際の指定係数射を、共通の表現の圏の二つの鎖複体の射として読む。 -/
def twoColorCoefficientChainMap (m n : ℕ) :
    (twoColorSourceResolutionCommon A m n).complex ⟶ (twoColorTargetResolution A m n).complex :=
  restrictionMap (representationCochainMap (twoColorSourceComplexAction A m n)
    (tensorComplexAction (twoColorLeftAction A m n) (twoColorRightAction A m n))
    (twoColorCoefficientComparison A m n) (twoColorCoefficientComparison_action A m n))
      ComplexShape.embeddingDownNat

end SerrePositivity.EInfinity.BarrattEccles
