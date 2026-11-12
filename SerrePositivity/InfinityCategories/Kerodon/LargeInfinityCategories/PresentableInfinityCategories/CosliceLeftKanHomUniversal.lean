module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ClassifiedCosliceHomRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftKanHomTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningEssentialSurjectivity

/-!
概要：指定 coslice 比較の分類は全 Hom の左 Kan 普遍性を持つ。
方針：実分類 Hom 制限の全単射性を、任意の標的の分類表示の余単位で移す。
規約：指定比較射を保持し、点ごとの同型の存在から推論しない。
使われ方：P-12 の指定共変 Hom 比較と Yoneda 単位の普遍性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (a : A _⦋0⦌)
local notation "sA" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm a)
local notation "sC" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)

local instance supplyCosliceLeftKanHomUniversal_pullbackLeftFibration
    {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p k) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：元の coslice 比較を分類した指定左 Kan 単位。
方針：元の実比較の分類に、指定底変換同型の逆を合成する。
規約：元の分類図式と実比較を保持する。使われ方：共変 Hom 単位の分類模型。 -/
def classifiedCosliceLeftKanUnit :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram sA)
      (((SSet.uliftFunctor.{u + 1, u}).map F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram sC) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom sA (pullback.snd sC F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceComparisonOver F a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceComparisonOver_projection F a) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso sC F).inv

/-- 概要：実分類 Hom 制限は指定左 Kan Hom 比較の底変換同型による後合成。
方針：元の正規化された前合成を展開し、合成の括弧を揃える。
規約：指定した同じ分類射を保持する。使われ方：全単射性の打ち消しによる移送。 -/
lemma classifiedCosliceHomRestriction_eq_leftKanHomMap
    {E : SSet.{u}} (p : E ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram sC)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.classifiedCosliceHomRestriction F a p α =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap ((SSet.uliftFunctor.{u + 1, u}).map F)
        (classifiedCosliceLeftKanUnit F a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p) α ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p F).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.classifiedCosliceHomRestriction, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap, classifiedCosliceLeftKanUnit,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap, eqToHom_refl, Category.id_comp,
    Category.comp_id, Category.assoc]

/-- 概要：指定 coslice 単位による分類済み標的への Hom 比較は全単射。
方針：分類 Hom 制限の全単射性から指定底変換同型を打ち消す。
規約：任意の元の left fibration が標的。使われ方：任意の標的の分類表示への適用。 -/
lemma classifiedCosliceLeftKanUnit_bijective_classifiedTarget
    {E : SSet.{u}} (p : E ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanHomMap ((SSet.uliftFunctor.{u + 1, u}).map F)
      (classifiedCosliceLeftKanUnit F a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.classifiedCosliceHomRestriction_bijective F a p
  constructor
  · intro α β hαβ
    apply h.injective
    rw [classifiedCosliceHomRestriction_eq_leftKanHomMap,
      classifiedCosliceHomRestriction_eq_leftKanHomMap, hαβ]
  · intro β
    obtain ⟨α, hα⟩ := h.surjective
      (β ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p F).hom)
    refine ⟨α, ?_⟩
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p F).hom).mp
    rwa [← classifiedCosliceHomRestriction_eq_leftKanHomMap]

/-- 概要：指定分類 coslice 単位による全 Hom 比較は左 Kan 普遍性を持つ。
方針：分類 Hom 制限の全単射性を標的の分類余単位で移送する。
規約：任意の全図式が標的であり、値ごとの判定へ弱めない。
使われ方：共変 Hom 比較と指定 Yoneda 単位の全 Hom 普遍性。 -/
lemma classifiedCosliceLeftKanUnit_homUniversal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal ((SSet.uliftFunctor.{u + 1, u}).map F)
      (classifiedCosliceLeftKanUnit F a) := by
  intro H
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKanHomMap_bijective_of_iso_target ((SSet.uliftFunctor.{u + 1, u}).map F)
    (classifiedCosliceLeftKanUnit F a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityCounit H)
    (classifiedCosliceLeftKanUnit_bijective_classifiedTarget F a
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection H))

/-- 概要：元の共変 Hom 比較は全 Hom の左 Kan 普遍性を持つ。
方針：指定 coslice 比較の分類模型を、元の共変表現可能図式の指定同型で移す。
規約：任意の F と a を扱い、比較射そのものの普遍性を主張する。
使われ方：P-12 の Hom 係数 Yoneda 単位の評価での普遍性。 -/
lemma covariantHomComparison_homUniversal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanHomUniversal ((SSet.uliftFunctor.{u + 1, u}).map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison F a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKanHomUniversal_iso_unit ((SSet.uliftFunctor.{u + 1, u}).map F)
    (classifiedCosliceLeftKanUnit F a)
    (classifiedCosliceLeftKanUnit_homUniversal F a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomTargetCosliceIso F a)
  simpa only [classifiedCosliceLeftKanUnit, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison, Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
