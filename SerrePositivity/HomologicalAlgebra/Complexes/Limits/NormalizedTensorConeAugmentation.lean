module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeComponents

/-!
概要：元の実 cone の各対象から同じ先端 X への augmentation と混合成分の像を構成する。
方針：先端では恒等、通常対象では同じ frame augmentation を使い、端点輸送を保持する。
規約：元の実対象・射・符号を保つ。使われ方：大域 augmentation 三角形の二重 cone。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorConeAugmentationAt {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 2)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj i ⟶ X := by
  induction i using Fin.cases with
  | zero => exact 𝟙 X
  | succ i => exact (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj i)

lemma normalizedTensorConeAugmentationAt_zero {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c 0 = 𝟙 X := rfl

lemma normalizedTensorConeAugmentationAt_succ {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c i.succ =
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj i) := rfl

lemma normalizedTensorConeAugmentationAt_postcompose_mixed {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (ha0 : a = 0) (h0 : 0 ∈ I) :
    HEq ((homPostcompose ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b)).f k
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).hom I a b k hI ha hb hk))
      ((homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app
        (c.obj ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0))))).f k
        (k.negOnePow • _root_.SerrePositivity.ComplexLimits.normalizedTensorElementSelectedCochainAtMax A X Y c (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) k
          (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0) (by have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h0; omega))) := by
  have ht : ∀ (a b : Fin (n + 2)) (j : Fin (n + 1)) (ha : a = 0) (hb : b = j.succ)
      (v : GradedHom A ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a)
        ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj b) k)
      (w : GradedHom A X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y).obj (c.obj j)) k),
      HEq v w → HEq ((homPostcompose ((_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).obj a)
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c b)).f k v)
        ((homPostcompose X ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A X Y).app (c.obj j))).f k w) := by
    intro a b j ha hb v w hv
    subst a
    subst b
    cases eq_of_heq hv
    rfl
  have hb' : b = ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0)).succ :=
    hb.trans (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withoutFirst I hI h0).symm
  exact ht a b _ ha0 hb' _ _
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_hom_mixed A X Y c I a b k hI ha hb hk ha0 h0)

lemma normalizedTensorConeAugmentationAt_quasiIso {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) (i : Fin (n + 2)) :
    QuasiIso (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c i) := by
  induction i using Fin.cases with
  | zero => change QuasiIso (𝟙 X); infer_instance
  | succ i => exact _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation_quasiIso A X Y (c.obj i)

lemma normalizedTensorConeAugmentationAt_reindex {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    HEq (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom i))
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeAugmentationAt A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) i) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

end SerrePositivity.ComplexLimits
