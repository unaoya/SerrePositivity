module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanHomCanonical
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.PresheafHomWeights
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanOppositeCanonicalLimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.UniverseRightKanCanonical

/-!
概要：標的全体を持ち上げた元の延長の全 Hom 族に、同じ宇宙の右 Kan 条件を与える。
方針：元の標準全余極限を宇宙同型で保持し、反転と元の全共同 Hom を適用する。
規約：空間宇宙変更の極限保存を仮定せず、元の標的と関手全体を持ち上げる。
使われ方：元の全自然変換空間族との、同じ宇宙・同じ Yoneda に沿う全自然比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 標的全体を持ち上げた元の全 Hom を、同じ全標的係数の族に束ねる。 -/
def sigmaLiftedHomFamily {C : SSet.{u}} {D : SSet.{u + 1}} [Quasicategory D]
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map
      (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 2, u + 1}).map G)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D)

/-- 元の指定単位から、持ち上げた元の関手の同じ標準全 Kan 余極限を得る。 -/
lemma sigmaLeftKan_ulift_canonicalColimits {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β) :
    ∀ v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))
        ((SSet.uliftFunctor.{u + 2, u + 1}).map G) v) := by
  rintro ⟨v⟩
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftKanCanonicalCocone_isColimit_iff_ulift _ _ _).mp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtension_canonicalColimits β hβ v)

/-- 元の持ち上げた全 Hom 族自身は、同じ宇宙の元の Yoneda の実際の右 Kan 延長。 -/
lemma sigmaLiftedHomFamily_isRightKanExtension {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G))
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) F₀ G β) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))))
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
          sigmaLiftedHomFamily G)
      (sigmaLiftedHomFamily G)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))) ≫
          sigmaLiftedHomFamily G)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanExtension_refl_post_ulift_of_canonicalLimits
  intro c
  have hc := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanCanonicalCone_op_isLimit _ _ (SSet.opObjEquiv c)
    (sigmaLeftKan_ulift_canonicalColimits β hβ (SSet.opObjEquiv c))
  have he : SSet.opObjEquiv.symm (SSet.opObjEquiv c) = c := Equiv.symm_apply_apply _ c
  rw [he] at hc
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coyonedaInfinityMap_map_isLimit _ hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
