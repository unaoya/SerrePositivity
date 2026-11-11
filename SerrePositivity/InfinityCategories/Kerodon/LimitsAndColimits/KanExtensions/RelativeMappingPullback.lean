module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHomPullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeFunctorMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：一般 U の相対 Kan 条件から四つの写像空間の引き戻しへの実際の比較同値。
方針：元の相対制限の片側比較に、相対標的の pinched Hom の引き戻し同型を合成する。
規約：右の底への射は前合成の Kan fibration なので厳密な引き戻しは homotopy pullback を計算する。
使われ方：Kerodon Proposition 7.3.6.7（Tag 030F） の元の四角形の表示。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：相対標的内の指定端点間の写像空間を計算する厳密な引き戻し。
方針：元の図式と底の図式の写像空間を、共通の底上の制限に沿って引き戻す。
規約：底の端点の等式による輸送は単体の値を保つ。
使われ方：四つの関手圏の写像空間の比較の標的。 -/
def kanRelativeMappingPullback {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((ihom K).map U)
    (s.fst.app _ (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))) (s.fst.app _ (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedPullbackRightMap s.isPullback.toCommSq
      (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)))

/-- 概要：相対標的の指定 pinched Hom は四つの写像空間の厳密な引き戻しと同型。
方針：任意の引き戻しの pinched Hom の普遍性を適用する。
規約：U の充填性は不要。
使われ方：相対制限の写像空間作用を実際の引き戻しへの比較へ移す。 -/
def kanRelativeMappingPullbackIso {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) ≅
      kanRelativeMappingPullback U δ s F G :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_isPullback s.isPullback _ _).isoPullback

/-- 概要：元の写像空間から四つの写像空間の引き戻しへの標準比較射。
方針：相対制限の作用と標的の引き戻し同型を合成する。
規約：指定された F と G 自身を両端に使う。
使われ方：一般 U の相対 Kan 条件の homotopy pullback の比較射。 -/
def kanRelativeMappingPullbackComparison {K C D E : SSet.{u}} (U : D ⟶ E) (δ : K ⟶ C)
    (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ⟶ kanRelativeMappingPullback U δ s F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap s.π _ _ ≫ (kanRelativeMappingPullbackIso U δ s F G).hom

/-- 概要：四つの写像空間の引き戻しは Kan 複体。
方針：単射上の相対標的の quasicategory 性と写像空間の同型で Kan 性を移す。
規約：U は任意。
使われ方：実際の単体的ホモトピー同値としての比較。 -/
lemma kanRelativeMappingPullback_kanComplex {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) [Mono δ]
    (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) :
    KanComplex (kanRelativeMappingPullback U δ s F G) := by
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono U δ s
  exact isFibrant_of_fibration (kanRelativeMappingPullbackIso U δ s F G).inv

/-- 概要：比較四角形の底への右の射は Kan fibration。
方針：前合成の inner 性による pinched 作用の Kan 性と端点輸送の同型を合成する。
規約：δ は単射、U は任意。
使われ方：厳密な引き戻しが homotopy pullback を計算することの入力。 -/
lemma kanRelativeMappingPullback_right_fibration {K C D E : SSet.{u}}
    [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) [Mono δ]
    (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedPullbackRightMap s.isPullback.toCommSq
      (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) (s.π.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))) := by
  change Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap ((pre δ).app E) _ _ ≫ _)
  infer_instance

/-- 概要：一般 U の左 Kan 条件から四つの写像空間の引き戻しへの比較はホモトピー同値。
方針：元の相対制限の片側比較に引き戻し同型を合成する。
規約：相手 G の普遍性や U の充填性は不要。
使われ方：相対 Kan の普遍写像性の左側の四角形。 -/
@[kerodon 030F]
lemma kanRelativeLeftMappingPullbackComparison_equivalence {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanRelativeMappingPullbackComparison U δ s F G) := by
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono U δ s
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  have : KanComplex (kanRelativeMappingPullback U δ s F G) :=
    kanRelativeMappingPullback_kanComplex U δ s F G
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (kanRelativeMappingPullbackIso U δ s F G)).isQCatEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftFunctor_relative_pinchedHomMap_equivalence_general δ hδ U s F G hF).comp
    he.isSimplicialHomotopyEquivalence

/-- 概要：一般 U の右 Kan 条件から四つの写像空間の引き戻しへの比較はホモトピー同値。
方針：右 Kan 関手へ入る元の相対制限の比較と引き戻し同型を合成する。
規約：始点 F の普遍性や U の充填性は不要。
使われ方：相対 Kan の普遍写像性の右側の四角形。 -/
@[kerodon 030F]
lemma kanRelativeRightMappingPullbackComparison_equivalence {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (U : D ⟶ E) (s : internalHom.PullbackObjObj δ U) (F G : C ⟶ D)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeRightKanExtendedFrom U δ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanRelativeMappingPullbackComparison U δ s F G) := by
  have : Quasicategory s.pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInternalHomTarget_quasicategory_of_mono U δ s
  have : Quasicategory ((internalHom.obj (Opposite.op C)).obj D) :=
    inferInstanceAs (Quasicategory ((ihom C).obj D))
  have : KanComplex (kanRelativeMappingPullback U δ s F G) :=
    kanRelativeMappingPullback_kanComplex U δ s F G
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (kanRelativeMappingPullbackIso U δ s F G)).isQCatEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeRightFunctor_relative_pinchedHomMap_equivalence_general δ hδ U s F G hG).comp
    he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
