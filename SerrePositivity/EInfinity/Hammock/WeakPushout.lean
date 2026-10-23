module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.WeakHomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Core.KanFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionMonoCobaseChange

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
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet
open SerrePositivity.InfinityCategories

lemma trivialKanFibration_pre_of_mono_weak {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (hf : IsWeakHomotopyEquivalence f) (Z : SSet.{u}) [KanComplex Z] :
    TrivialKanFibration ((pre f).app Z) :=
  trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence _
    (F2.pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence f hf Z)

/-- 元の弱同値が単射なら、任意の相手側への元の pushout で保存される。 -/
lemma weakPushout_mono {A B C D : SSet.{u}} {i : A ⟶ B} [Mono i]
    {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (hi : IsWeakHomotopyEquivalence i) (h : IsPushout i g k j) :
    IsWeakHomotopyEquivalence j := by
  intro Z hZ
  have := trivialKanFibration_pre_of_mono_weak i hi Z
  have : TrivialKanFibration ((pre j).app Z) :=
    ⟨trivialKanFibrations.of_isPullback (isPullback_pre_of_isPushout h Z).flip
      (TrivialKanFibration.mem (p := (pre i).app Z))⟩
  have he := isQCatEquivalence_of_trivialKanFibration ((pre j).app Z)
  exact he.isSimplicialHomotopyEquivalence.mapPiZero_bijective

/-- 相手側が単射なら、単射とは限らない元の弱同値も元の pushout で保存される。 -/
lemma weakPushout_other_mono {A B C D : SSet.{u}} {i : A ⟶ B} {g : A ⟶ C} [Mono g]
    {k : B ⟶ D} {j : C ⟶ D} (hi : IsWeakHomotopyEquivalence i)
    (h : IsPushout i g k j) : IsWeakHomotopyEquivalence j := by
  intro Z hZ
  have : TrivialKanFibration (relativeEquivalencePathMapAt ((pre g).app Z) 1) :=
    trivialKanFibration_relativeEquivalencePathMapAt_pre g Z 1
  have hi' := (F2.pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence i hi Z)
    |> IsSimplicialHomotopyEquivalence.isQCatEquivalence
  have hp := hi'.pullback_snd_of_relativePath ((pre g).app Z)
  have hpb := (isPullback_pre_of_isPushout h Z).flip
  have he := hpb.isoPullback_hom_snd
  have hq : IsQCatEquivalence ((pre j).app Z) := by
    rw [← he]
    exact (qCatEquivalenceOfIso hpb.isoPullback).isQCatEquivalence.comp hp
  exact hq.isSimplicialHomotopyEquivalence.mapPiZero_bijective

end SerrePositivity.EInfinity.Hammock
