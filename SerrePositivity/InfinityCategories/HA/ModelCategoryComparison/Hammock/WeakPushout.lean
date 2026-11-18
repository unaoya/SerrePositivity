module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.WeakHomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.KanFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionMonoCobaseChange

/-!
# 元の弱ホモトピー同値の pushout による保存

概要：弱同値が単射、または相手側が単射なら、元の pushout の比較射は弱同値。
方針：Kan 標的を固定し、前合成の trivial Kan fibration または相対 path の持ち上げを使う。
規約：単体集合のモデル構造や元の対象の Kan 性を入力にしない。
使われ方：proper 図式の段階と境界の貼り合わせ。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalClosed _root_.SSet
open _root_.SerrePositivity.InfinityCategories

lemma trivialKanFibration_pre_of_mono_weak {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f) (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre f).app Z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence f hf Z)

/-- 元の弱同値が単射なら、任意の相手側への元の pushout で保存される。 -/
lemma weakPushout_mono {A B C D : SSet.{u}} {i : A ⟶ B} [Mono i]
    {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence i) (h : IsPushout i g k j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence j := by
  intro Z hZ
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.trivialKanFibration_pre_of_mono_weak i hi Z
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre j).app Z) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout h Z).flip
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := (pre i).app Z))⟩
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration ((pre j).app Z)
  exact he.isSimplicialHomotopyEquivalence.mapPiZero_bijective

/-- 相手側が単射なら、単射とは限らない元の弱同値も元の pushout で保存される。 -/
lemma weakPushout_other_mono {A B C D : SSet.{u}} {i : A ⟶ B} {g : A ⟶ C} [Mono g]
    {k : B ⟶ D} {j : C ⟶ D} (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence i)
    (h : IsPushout i g k j) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence j := by
  intro Z hZ
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt ((pre g).app Z) 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_relativeEquivalencePathMapAt_pre g Z 1
  have hi' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence i hi Z)
    |> _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isQCatEquivalence
  have hp := hi'.pullback_snd_of_relativePath ((pre g).app Z)
  have hpb := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPullback_pre_of_isPushout h Z).flip
  have he := hpb.isoPullback_hom_snd
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre j).app Z) := by
    rw [← he]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso hpb.isoPullback).isQCatEquivalence.comp hp
  exact hq.isSimplicialHomotopyEquivalence.mapPiZero_bijective

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
