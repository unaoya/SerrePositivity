module

public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Core.LimitDiagramIso
public import SerrePositivity.InfinityCategories.F2.Presentable.FullyFaithfulHomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitMappingComparison
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.F1B.Cones.CosliceOpposite

/-!
概要：元の充満忠実関手は指定した全錐の極限性・余極限性を反映する。
方針：全共変 Hom の自然比較によって極限を反映し、余極限は同じ全余錐の反転で戻す。
規約：形状は任意で、指定された元の全錐を保持する。
使われ方：Hom の小さい模型と指定宇宙変更から元の保存性を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：充満忠実な元の関手は指定全錐の極限性を反映する。
方針：像の全 Hom 極限を元の共変 Hom へ全自然同型で戻す。
規約：元の形状に充填性を要求しない。
使われ方：小さい Hom 模型への極限保存性の回収。 -/
lemma isLimitCone_of_fullyFaithful_image {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (F : C ⟶ D) (hF : IsFullyFaithful F)
    {a : K ⟶ C} (c : JoinCone a) (hc : IsLimitCone (mapJoinCone F c)) : IsLimitCone c := by
  apply (isLimitCone_iff_covariantRepresentableInfinity c).mpr
  intro x
  have h := covariantRepresentableInfinity_isLimit (mapJoinCone F c) hc
    (F.app _ x)
  rw [← mapJoinCone_universe_comp] at h
  exact h.of_functorIso ((covariantHomComparisonIso F hF x).precomp (JoinCone.ulift c).val).symm

/-- 概要：全余錐の反転と関手の後合成は元の全射で可換。
方針：反転の全射の公式で同じ後合成を計算する。
規約：図式と標的の充填性を要求しない。
使われ方：極限の反映から余極限の反映への双対化。 -/
lemma coconeReverseCone_postcomp_val {K C D : SSet.{u}} {a : K ⟶ C}
    (F : C ⟶ D) (c : JoinCocone a) :
    (F1B.coconeReverseCone c).val ≫ SSet.opFunctor.map F =
      (F1B.coconeReverseCone (mapJoinCocone F c)).val := by
  rw [F1B.coconeReverseCone_val, F1B.coconeReverseCone_val]
  simp only [mapJoinCocone, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：充満忠実な元の関手は指定全余錐の余極限性を反映する。
方針：同じ全余錐を反転して全極限の反映へ渡す。
規約：元の全余錐そのものの普遍性を結論する。
使われ方：小さい Hom 模型への filtered 余極限保存性の回収。 -/
lemma isColimitCone_of_fullyFaithful_image {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (F : C ⟶ D) (hF : IsFullyFaithful F)
    {a : K ⟶ C} (c : JoinCocone a) (hc : IsColimitCone (mapJoinCocone F c)) :
    IsColimitCone c := by
  apply (F1B.isColimitCone_iff_reverseCone c).mpr
  apply isLimitCone_of_fullyFaithful_image (SSet.opFunctor.map F)
    (Idempotent.isFullyFaithful_op_of_fullyFaithful F hF) (F1B.coconeReverseCone c)
  exact (F2.isLimitCone_iff_of_cone_val_eq _ _ (coconeReverseCone_postcomp_val F c)).mpr
    ((F1B.isColimitCone_iff_reverseCone (mapJoinCocone F c)).mp hc)

end SerrePositivity.InfinityCategories.F2.Presentable
