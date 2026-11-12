module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：小さい sifted 余極限保存の恒等と合成。
方針：同じ全余錐の像を全余錐の射の等式で照合する。
規約：指定余錐を選び直さない。
使われ方：有限余積の各座標の関手族の保存条件。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories


/-- 概要：恒等関手は元の全小さい sifted 余極限を保存する。
方針：同じ全余錐を回収する。
規約：元の全余錐を保持する。
使われ方：更新する座標の保存条件。 -/
lemma identity_preservesSmallSiftedColimits (X : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits (𝟙 X) := by
  intro I hI p c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.comp_id c.val)).mpr hc

/-- 概要：小さい sifted 余極限を保つ二関手の合成も同じ余極限を保存する。
方針：同じ全余錐を二度写す。
規約：像の全余錐の射の等式で比較する。
使われ方：座標更新と全比較関手の合成。 -/
lemma preservesSmallSiftedColimits_comp {X Y Z : SSet.{u + 1}}
    {F : X ⟶ Y} {G : Y ⟶ Z} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits F)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits (F ≫ G) := by
  intro I hI p c hc
  have h := hG I _ _ (hF I p c hc)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc c.val F G).symm).mpr h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
