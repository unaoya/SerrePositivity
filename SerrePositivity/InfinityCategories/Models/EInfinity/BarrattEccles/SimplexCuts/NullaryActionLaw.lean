module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainNullaryAction

/-!
模型。文献の定義との比較は後で
# 空語余作用と指定augmentationの複体射の一致

Berger–Fresse §1.2.1・§2.2.6、M14 L14、報告 §386。
構成に使った同じ零arity成分をtensorLiftの外延性で戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- L14の零作用は指定した係数augmentationとAW余単位のテンソル（BF §2.2.6）。 -/
lemma coaction_nullary (S : SSet.{0}) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S 0 =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientAugmentation A ⊗ₘ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A S) ≫
        (λ_ (𝟙_ (Complex A))).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_zero_eq_nullaryAction, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryAction, tensorHom_def, Category.assoc,
    leftUnitor_naturality]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
