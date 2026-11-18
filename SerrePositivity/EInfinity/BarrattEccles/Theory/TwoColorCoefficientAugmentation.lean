module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCoefficientMap
public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryPrefixAugmentation

/-!
# 二色の指定係数比較と増大

## 概要
HA 3.2.4.7 の実際の二色係数比較射が、指定された増大を保つことを示す。

## 方針
両色への射影が増大を保つことと、Hopf 対角の左余単位則を組み合わせる。

## 規約
射影解像度の指定増大と、元の `complexAugmentation` を同じ射として照合する。

## 使われ方
実際の係数比較射の等変な鎖ホモトピー逆。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory

/-- 左余単位則から、二つの因子を共に増大した対角の式を得る。 -/
lemma diagonal_tensor_counit {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {X : C} (δ : X ⟶ X ⊗ X) (ε : X ⟶ 𝟙_ C)
    (h : δ ≫ (ε ▷ X) ≫ (λ_ X).hom = 𝟙 X) :
    δ ≫ (ε ⊗ₘ ε) ≫ (λ_ (𝟙_ C)).hom = ε := by
  have hh := congrArg (fun f => f ≫ ε) h
  simp only [Category.assoc, Category.id_comp] at hh
  rw [tensorHom_def]
  simp only [Category.assoc]
  rw [leftUnitor_naturality]
  exact hh

namespace BarrattEccles
open SerrePositivity.DifferentialGraded
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level operad sequence
variable (A : Type u) [CommRing A]

/-- 右側の色への指定射影は増大を保つ。 -/
lemma twoColorRightCoefficient_augmentation (m n : ℕ) :
    twoColorRightCoefficient A m n ≫ (augmentation A).map.app (FiniteBijection.of n) =
      (augmentation A).map.app (FiniteBijection.of (m + n)) :=
  nullaryPrefixDelete_augmentation A m n

/-- 左側の色への指定射影も、ブロック交換の自然性によって増大を保つ。 -/
lemma twoColorLeftCoefficient_augmentation (m n : ℕ) :
    twoColorLeftCoefficient A m n ≫ (augmentation A).map.app (FiniteBijection.of m) =
      (augmentation A).map.app (FiniteBijection.of (m + n)) := by
  have h := (augmentation A).map.naturality
    (FiniteBijection.homOfEquiv (X := FiniteBijection.of (m + n))
      (Y := FiniteBijection.of (n + m)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n))
  change (operad A).arityBijectionMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n) ≫
    (augmentation A).map.app (FiniteBijection.of (n + m)) =
      (augmentation A).map.app (FiniteBijection.of (m + n)) ≫ 𝟙 _ at h
  unfold twoColorLeftCoefficient
  rw [Category.assoc, nullaryPrefixDelete_augmentation]
  exact h.trans (Category.comp_id _)

/-- Hopf 対角と両射影からなる実際の係数比較は、指定増大を保つ。 -/
lemma twoColorCoefficientComparison_augmentation (m n : ℕ) :
    twoColorCoefficientComparison A m n ≫ twoColorTensorAugmentation A m n =
      complexAugmentation A (m + n) := by
  have ht : (twoColorLeftCoefficient A m n ⊗ₘ twoColorRightCoefficient A m n) ≫
      ((augmentation A).map.app (FiniteBijection.of m) ⊗ₘ
        (augmentation A).map.app (FiniteBijection.of n)) =
      ((augmentation A).map.app (FiniteBijection.of (m + n)) ⊗ₘ
        (augmentation A).map.app (FiniteBijection.of (m + n))) := by
    rw [tensorHom_comp_tensorHom, twoColorLeftCoefficient_augmentation,
      twoColorRightCoefficient_augmentation]
  rw [twoColorTensorAugmentation_eq, ← augmentation_app A m, ← augmentation_app A n]
  unfold twoColorCoefficientComparison
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  exact diagonal_tensor_counit _ _ ((hopf A).left_counit (m + n))

end BarrattEccles
end SerrePositivity.EInfinity
