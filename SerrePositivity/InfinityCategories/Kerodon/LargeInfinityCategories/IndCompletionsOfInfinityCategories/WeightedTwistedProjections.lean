module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedTwistedPullbackCoefficient

/-!
概要：元の twisted-arrow 引き戻しの weighted 全空間から、元の二つの射影を読む。
方針：各段の引き戻しの両射影を自然変換へ束ね、最後の係数評価で可換性を計算する。
規約：底と添字を厳密に保持。使われ方：weighted 全空間の同じ引き戻しとしての同定。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} {I : Type u} [SmallCategory I]
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject C)

/-- 元の各段の twisted-arrow 底を、元の定値図式へ同時に射影する。 -/
def strictRightTwistedBaseProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedElementsDiagram F ⟶
    (CategoryTheory.Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision C) where
  app i := pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) (F.obj i).val.hom
  naturality i j f := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _ ≫ 𝟙 _
    rw [pullback.lift_fst, Category.comp_id]

/-- 元の各段の全空間を、同じ元の通常図式へ同時に射影する。 -/
def strictRightTwistedTotalProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedElementsDiagram F ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F where
  app i := pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C) (F.obj i).val.hom
  naturality i j f := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    exact pullback.lift_snd _ _ _

/-- 全 twisted arrow の同じ底への射影。 -/
def weightedTwistedBaseProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedElementsDiagram F) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision C := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (strictRightTwistedBaseProjection F)

/-- 元の weighted 全空間への同じ第二射影。 -/
def weightedTwistedTotalProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightTwistedElementsDiagram F) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationTotalDiagram F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (strictRightTwistedTotalProjection F)

/-- 同じ全射影は元の底の終点射影と元の密度の底射影を厳密に結ぶ。 -/
lemma weightedTwistedProjections_commute :
    weightedTwistedBaseProjection F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C =
      weightedTwistedTotalProjection F ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationProjectionCocone F).ι := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight C).app _
      (SSet.yonedaEquiv (s.2.app (Fin.last n) ≫ pullback.fst _ _)) =
    SSet.yonedaEquiv ((s.2.app (Fin.last n) ≫ pullback.snd _ _) ≫
      (F.obj (s.1.obj (Fin.last n))).val.hom)
  rw [← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  rw [Category.assoc, pullback.condition, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
