module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CosliceTwistedArrowNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationBaseChangeHom
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EndSectionsRelativeHom
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowFunctorComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
概要：指定共同Hom単位を始点固定で評価するときの、同じ実引き戻しの係数模型。
方針：引き戻しの貼り合わせを二通りに行い、始点固定の底の可換式で結ぶ。
規約：同型の両射影と元のTw(F)の全空間写像を保持する。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3を基礎とする
指定Yoneda左Kan単位の前層成分の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
open ClassificationOfCocartesianFibrations.F1FibrationsFiberComparisonBaseChange
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
open PresentableInfinityCategories
variable {A C : SSet.{u}}

/-- 概要：始点固定した共同Homの底変換は、同じ始点固定Hom射影のFによる底変換と同型。
方針：通常の引き戻しの貼り合わせを使う。規約：任意の単体集合と元のF・aを保つ。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3を基礎とする
指定単位の係数移送。引用した命題そのものではなく、その実写像の計算。 -/
def homWeightYonedaSourcePullbackIso (F : A ⟶ C) (a : A _⦋0⦌) :
    pullback (functorHomBifunctorProjection F F) (twistedArrowSourceInclusion a) ≅
      pullback (twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)) F :=
  pullbackLeftPullbackSndIso (twistedArrowProjection C)
      (SSet.opFunctor.map F ⊗ₘ F) (twistedArrowSourceInclusion a) ≪≫
    pullback.congrHom rfl (twistedArrowSourceInclusion_postcomp F a) ≪≫
      (pullbackLeftPullbackSndIso (twistedArrowProjection C)
        (twistedArrowSourceInclusion (F.app (Opposite.op ⦋0⦌) a)) F).symm

/-- 概要：同じ移送は元のtwisted arrow全空間への第一射影を保つ。
方針：貼り合わせ同型の射影則を使う。規約：元のFとaを保つ。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3を基礎とする
単位の実写像の照合。引用した命題そのものではなく、その射影の計算。 -/
lemma homWeightYonedaSourcePullbackIso_hom_fst_fst (F : A ⟶ C) (a : A _⦋0⦌) :
    (homWeightYonedaSourcePullbackIso F a).hom ≫
        pullback.fst (twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)) F ≫
          pullback.fst (twistedArrowProjection C)
            (twistedArrowSourceInclusion (F.app (Opposite.op ⦋0⦌) a)) =
      pullback.fst (functorHomBifunctorProjection F F) (twistedArrowSourceInclusion a) ≫
        pullback.fst (twistedArrowProjection C) (SSet.opFunctor.map F ⊗ₘ F) := by
  simp [homWeightYonedaSourcePullbackIso, twistedArrowSourceProjection,
    functorHomBifunctorProjection, functorHomBifunctorBase, Category.assoc]

/-- 概要：同じ移送は元のAへの第二射影を保つ。
方針：貼り合わせ同型の射影則を使う。規約：元のFとaを保つ。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3を基礎とする
単位の実写像の照合。引用した命題そのものではなく、その底の計算。 -/
lemma homWeightYonedaSourcePullbackIso_hom_snd (F : A ⟶ C) (a : A _⦋0⦌) :
    (homWeightYonedaSourcePullbackIso F a).hom ≫
        pullback.snd (twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)) F =
      pullback.snd (functorHomBifunctorProjection F F) (twistedArrowSourceInclusion a) := by
  simp [homWeightYonedaSourcePullbackIso, twistedArrowSourceProjection,
    functorHomBifunctorProjection, functorHomBifunctorBase, Category.assoc]

/-- 概要：指定Tw(F)の始点固定底変換は同じ始点固定後合成の持ち上げと一致する。
方針：両射影で検出し、既存の後合成の式を使う。規約：元の実写像を保つ。
使われ方：Kerodon Tag 03M5・03W8、HTT 5.1.3.1・5.1.5.3を基礎とする
単位の分類前の可換正方形。引用した命題そのものではなく、同じ射の照合。 -/
lemma homWeightYonedaSourcePullbackIso_postcomp (F : A ⟶ C) (a : A _⦋0⦌) :
    fiberComparisonBaseChange (twistedArrowProjection A) (functorHomBifunctorProjection F F)
        (twistedArrowFunctorComparison F) (twistedArrowFunctorComparison_projection F)
        (twistedArrowSourceInclusion a) ≫ (homWeightYonedaSourcePullbackIso F a).hom =
      pullback.lift (twistedArrowSourcePostcomp F a) (twistedArrowSourceProjection a)
        (twistedArrowSourcePostcomp_projection F a) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, homWeightYonedaSourcePullbackIso_hom_fst_fst,
        pullback.lift_fst, twistedArrowSourcePostcomp_fst]
      simp [fiberComparisonBaseChange, twistedArrowFunctorComparison, Category.assoc]
    · simp only [Category.assoc, pullback.lift_fst]
      change _ ≫ (homWeightYonedaSourcePullbackIso F a).hom ≫
          pullback.fst (twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)) F ≫
            twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a) =
        twistedArrowSourcePostcomp F a ≫
          twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)
      rw [pullback.condition]
      rw [← Category.assoc (homWeightYonedaSourcePullbackIso F a).hom
        (pullback.snd (twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a)) F) F,
        homWeightYonedaSourcePullbackIso_hom_snd]
      simp only [← Category.assoc, fiberComparisonBaseChange_projection,
        twistedArrowSourcePostcomp_projection]
      rfl
  · simp only [Category.assoc, homWeightYonedaSourcePullbackIso_hom_snd,
      fiberComparisonBaseChange_projection, pullback.lift_snd]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion
