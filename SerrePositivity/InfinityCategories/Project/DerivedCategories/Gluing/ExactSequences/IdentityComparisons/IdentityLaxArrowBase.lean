module
public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
/-!
概要：恒等二脚の基底変更を、全矢印族への後合成で構成する。
方針：恒等 lax 圏と矢印圏の厳密同型を用い、指定基底同値を全単体で後合成する。
規約：恒等対角との厳密可換性を保持する。使われ方：恒等対角・cone 全比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet
open _root_.SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]

def identityLaxArrowBaseEquivalence (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (𝟙 X) (𝟙 X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (𝟙 Y) (𝟙 Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso X)).trans
    ((e.isQCatEquivalence.postcompose (Δ[1] : SSet.{u})).choose.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxIso Y).symm))

lemma identityLaxArrowBaseEquivalence_diagonal (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X) ≫
      (identityLaxArrowBaseEquivalence e).hom =
    e.hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) Y ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Y) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) X ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e.hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Y) = _
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse X), _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_arrow,
    Category.id_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_postcomp, Category.assoc]

lemma identityLaxArrowBaseEquivalence_arrow (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) :
    (identityLaxArrowBaseEquivalence e).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Y) (𝟙 Y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e.hom := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X) ≫ (ihom (Δ[1] : SSet.{u})).map e.hom ≫
    _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse Y) ≫ _ = _
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_arrow, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
