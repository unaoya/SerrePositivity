module

public import SerrePositivity.InfinityCategories.F2.Presentable.SpaceRightAdjointContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.AdjointFunctorTheorem
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorPresentable
public import SerrePositivity.InfinityCategories.F2.Presentable.SpacePresentable
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantHomFaithful

/-!
概要：小さい図式の極限を与える右随伴と、その指定濃度の filtered 保存を構成する。
方針：定値図式の各点余極限保存から随伴関手定理を適用し、一点像の compact 性を使う。
規約：非可算正則 μ と μ-small な quasicategory 形状に対し、同じ μ の保存性を結論する。
使われ方：小さい coherent 極限と filtered 余極限の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：定値図式関手は全小余極限を保存する。
方針：各評価との合成を恒等関手に戻し、各点の余極限判定を適用する。
規約：図式の始域 A は大きくてもよく、その quasicategory 性は要求しない。
使われ方：定値図式関手の右随伴の構成。 -/
lemma constantFunctorMap_preservesSmallColimits (A : SSet.{u + 1})
    {C : SSet.{u + 1}} [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (constantFunctorMap A C) := by
  intro J D c hc
  apply isColimitCone_of_pointwise
  intro a
  have hv : (evaluateFunctorCocone (mapJoinCocone (constantFunctorMap A C) c) a).val =
      c.val := by
    change (c.val ≫ constantFunctorMap A C) ≫ evaluateFunctorAt a = c.val
    rw [Category.assoc, constantFunctorMap_evaluate, Category.comp_id]
  exact (isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr hc

/-- 概要：小さい quasicategory 上の空間値図式には定値図式の右随伴が存在する。
方針：空間とその全関手圏の presentable 性、および定値図式の余極限保存を使う。
規約：極限の存在や関手の選択を追加入力にしない。
使われ方：全自然な極限関手の選択。 -/
lemma exists_spaceLimitFunctor (B : SSet.{u}) [Quasicategory B] :
    ∃ R : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶
        SpaceInfinity.{u},
      Nonempty (QCatAdjunction
        (constantFunctorMap ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) R) :=
  (exists_rightAdjoint_iff_preservesSmallColimits space_isPresentable
    (functor_isPresentable B space_isPresentable) _).mpr
      (constantFunctorMap_preservesSmallColimits _)

/-- 概要：μ-small な形状の空間値極限関手を、同じ μ の filtered 保存とともに構成する。
方針：右随伴の存在と、一点定値図式の compact 性による保存判定を結合する。
規約：元の μ を拡大せず、一般の accessibility だけで代用しない。
使われ方：小極限の族の μ-filtered 保存。 -/
lemma exists_kappaContinuousSpaceLimitFunctor
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (B : SSet.{u}) [Quasicategory B] (hB : IsKappaSmall μ B) :
    ∃ R : (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u} ⟶
        SpaceInfinity.{u},
      Nonempty (QCatAdjunction
        (constantFunctorMap ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) R) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ R := by
  obtain ⟨R, ⟨a⟩⟩ := exists_spaceLimitFunctor B
  exact ⟨R, ⟨a⟩, constantFunctor_rightAdjoint_isKappaAccessibleFunctor hμ B hB a⟩

end SerrePositivity.InfinityCategories.F2.Presentable
