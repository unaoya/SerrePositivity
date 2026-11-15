module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorizationLimitComparison

/-!
概要：元の各引き戻し篩で降下するとき、元の篩と交叉篩の降下は同値。
方針：指定右 Kan の全錐比較と、二段分解から交叉への既存の left cofinal 射を合成する。
使われ方：HTT 6.2.2.6、Kerodon §7.3（Tag 02Y1）の生成系からの降下。
規約：任意の準圏係数。極限の存在を追加仮定せず、元の restrictionCone を結論する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 各 S の引き戻しで降下すれば、元の R と R ⊓ S の指定制限錐の極限性は同値。 -/
lemma restrictionCone_inf_isLimit_iff_of_pullbacks (R S : Sieve U)
    {E : SSet.{u + 1}} [Quasicategory E] (F : Presheaf C E)
    (hF : ∀ t : sieveCategory R, IsLimitCone (restrictionCone F (S.pullback t.obj.hom))) :
    IsLimitCone (restrictionCone F (R ⊓ S)) ↔ IsLimitCone (restrictionCone F R) := by
  let j := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (sieveFactorizationComposite R S).op)
  have hj : IsLeftCofinal j :=
    isLeftCofinal_ulift _ (sieveFactorizationComposite_op_isLeftCofinal R S)
  have hv := uliftNerveCone_whisker_val (sieveCone (R ⊓ S))
    (sieveFactorizationComposite R S).op F
  exact (isLimitCone_iff_restrict_of_leftCofinal j hj _ _).trans
    ((SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ hv).trans
      (sieveFactorizationCone_isLimit_iff R S F hF).symm)

end SerrePositivity.InfinityCategories.Sheaves
