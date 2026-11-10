module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndYonedaHomEvaluation
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallHomCompositeContinuity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits

/-!
概要：Ind 値の元の関手の filtered 保存を元の Yoneda Hom の小さい族で検出する。
方針：全 Hom 比較で前層評価へ移し、各点余極限と全部分包含による反映を使う。
規約：指定宇宙変更の充満忠実性は比較用の明示入力。
使われ方：右随伴の accessibility を共通 compact 濃度から導く。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全 Yoneda Hom 合成の元の filtered 保存から Ind 値の関手の保存性を反映する。
方針：小さい各評価の保存性を回収し、元の指定像余錐の各点普遍性を検査する。
規約：μ と κ の間に順序や交換条件を仮定しない。
使われ方：共通 Hom 濃度による右随伴の元の accessibility の判定。 -/
lemma isKappaAccessibleFunctor_of_indHomTests
    (hU : IsFullyFaithful Compact.spaceUniverseDiagram.{u}) (κ μ : Cardinal.{u})
    (A : SSet.{u}) [Quasicategory A] {D : SSet.{u + 1}}
    (G : D ⟶ Ind.IndInfinity κ A)
    (hG : ∀ a : A _⦋0⦌, Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫ covariantRepresentableInfinity
        ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G := by
  intro I hI hμ F c hc
  apply isColimitCone_of_fullyFaithful_image (Ind.indInclusionPresheaf κ A)
    (Ind.indInclusionPresheaf_isFullyFaithful κ A) (mapJoinCocone G c)
  apply presheafInfinity_isColimit_of_evaluation _ _
  intro a
  let H := Ind.indInclusionPresheaf κ A ≫ presheafInfinityEvaluation a
  have ht := (hG a).of_functorIso (smallHomCompositeIso G
    ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)) H
    (indYonedaHom_evaluationIso κ A a))
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (G ≫ H) :=
    isKappaAccessibleFunctor_of_spaceUniverse hU ht
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ (by
    simp only [H, mapJoinCocone, Category.assoc])).mpr (hn I F c hc)

end SerrePositivity.InfinityCategories.F2.Presentable
