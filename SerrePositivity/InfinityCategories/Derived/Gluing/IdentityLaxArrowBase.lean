module
public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor
public import SerrePositivity.InfinityCategories.F1.Categories.QCatSimplicial
/-!
概要：恒等二脚の基底変更を、全矢印族への後合成で構成する。
方針：恒等 lax 圏と矢印圏の厳密同型を用い、指定基底同値を全単体で後合成する。
規約：恒等対角との厳密可換性を保持する。使われ方：恒等対角・cone 全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

def identityLaxArrowBaseEquivalence (e : QCatEquivalence X Y) :
    QCatEquivalence (F2.laxPullback (𝟙 X) (𝟙 X)) (F2.laxPullback (𝟙 Y) (𝟙 Y)) :=
  (qCatEquivalenceOfIso (arrowLaxIso X)).trans
    ((e.isQCatEquivalence.postcompose (Δ[1] : SSet.{u})).choose.trans
      (qCatEquivalenceOfIso (arrowLaxIso Y).symm))

lemma identityLaxArrowBaseEquivalence_diagonal (e : QCatEquivalence X Y) :
    (constantFunctorMap (Δ[1] : SSet.{u}) X ≫ arrowLaxInverse X) ≫
      (identityLaxArrowBaseEquivalence e).hom =
    e.hom ≫ (constantFunctorMap (Δ[1] : SSet.{u}) Y ≫ arrowLaxInverse Y) := by
  change (constantFunctorMap (Δ[1] : SSet.{u}) X ≫ arrowLaxInverse X) ≫
    (F2.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e.hom ≫
      arrowLaxInverse Y) = _
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse X), _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse_arrow,
    Category.id_comp, ← Category.assoc, constantFunctorMap_postcomp, Category.assoc]

lemma identityLaxArrowBaseEquivalence_arrow (e : QCatEquivalence X Y) :
    (identityLaxArrowBaseEquivalence e).hom ≫ F2.laxPullbackArrow (𝟙 Y) (𝟙 Y) =
      F2.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e.hom := by
  change (F2.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e.hom ≫
    arrowLaxInverse Y) ≫ _ = _
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.StablePresentable.Quasicategory.arrowLaxInverse_arrow, Category.comp_id]

end SerrePositivity.InfinityCategories
