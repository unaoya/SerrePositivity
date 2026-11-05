module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.RelativeSimplexAttachment

/-!
概要：実貼合せ境界の相対図式と、元の全商図式を同時に保持する比較。
方針：厳密な商可換四角形から同じ pullback への射を作り、両射影の実同値で比較する。
規約：この同値は貼合せ工程の比較。c5 の商射そのものの同値とは区別する。
使われ方：共有経路と商比較を記憶した全パラメータ族の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Localization
open SerrePositivity.KST.LocalizingInvariants
variable {B C : SSet.{u}} [Quasicategory B] [Quasicategory C] (q : B ⟶ C) (n : ℕ)

instance simplexAttachmentCoreRestriction_trivialKanFibration :
    TrivialKanFibration (quasicategoryCoreMap ((pre (simplexAttachmentBoundary n).ι).app C)) :=
  F2.coreMap_trivialKanFibration _

/-- 元の全商図式と、その境界を持つ元の相対図式の厳密 pullback。 -/
def simplexAttachmentQuotientPullback : SSet.{u} :=
  pullback (quasicategoryCoreMap ((pre (simplexAttachmentBoundary n).ι).app C))
    (relativeFunctorCoreQuotient q (simplexAttachmentBoundary n : SSet.{u}))

def simplexAttachmentQuotientPullbackProjection : simplexAttachmentQuotientPullback q n ⟶
    (relativeFunctorCore q (simplexAttachmentBoundary n : SSet.{u}) : SSet.{u}) :=
  pullback.snd _ _

instance simplexAttachmentQuotientPullbackProjection_trivialKanFibration :
    TrivialKanFibration (simplexAttachmentQuotientPullbackProjection q n) :=
  trivialKanFibration_pullback_snd _ _

instance simplexAttachmentQuotientPullback_quasicategory :
    Quasicategory (simplexAttachmentQuotientPullback q n) :=
  quasicategory_of_innerFibration (simplexAttachmentQuotientPullbackProjection q n)

/-- 同じ元の商射と同じ実制限射を二脚に持つ、指定された比較。 -/
def simplexAttachmentQuotientComparison :
    (relativeFunctorCore q (join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) ⟶
      simplexAttachmentQuotientPullback q n :=
  pullback.lift (relativeFunctorCoreQuotient q (join (Δ[n] : SSet.{u}) Δ[0]))
    (relativeSimplexAttachmentRestriction q n) (relativeSimplexAttachmentQuotient_square q n).symm

omit [Quasicategory B] in
lemma simplexAttachmentQuotientComparison_quotient :
    simplexAttachmentQuotientComparison q n ≫ pullback.fst _ _ =
      relativeFunctorCoreQuotient q (join (Δ[n] : SSet.{u}) Δ[0]) :=
  pullback.lift_fst _ _ _

omit [Quasicategory B] in
lemma simplexAttachmentQuotientComparison_boundary :
    simplexAttachmentQuotientComparison q n ≫ simplexAttachmentQuotientPullbackProjection q n =
      relativeSimplexAttachmentRestriction q n :=
  pullback.lift_snd _ _ _

/-- 同じ商比較を保持する実貼合せ工程の比較は、全 Hom の意味で同値。 -/
lemma simplexAttachmentQuotientComparison_isQCatEquivalence :
    IsQCatEquivalence (simplexAttachmentQuotientComparison q n) := by
  have hp := isQCatEquivalence_of_trivialKanFibration
    (simplexAttachmentQuotientPullbackProjection q n)
  have hc : IsQCatEquivalence (simplexAttachmentQuotientComparison q n ≫
      simplexAttachmentQuotientPullbackProjection q n) := by
    rw [simplexAttachmentQuotientComparison_boundary]
    exact isQCatEquivalence_of_trivialKanFibration _
  exact hp.cancel_right hc

/-- 全図式と商比較を記憶する可逆経路置換。 -/
def simplexAttachmentQuotientResolution : SSet.{u} :=
  equivalencePathReplacement (simplexAttachmentQuotientComparison q n)

def simplexAttachmentQuotientResolutionMap : simplexAttachmentQuotientResolution q n ⟶
    simplexAttachmentQuotientPullback q n :=
  equivalencePathReplacementMap _

/-- 経路置換から、元の同じ全相対図式を回収する。 -/
def simplexAttachmentQuotientResolutionSource : simplexAttachmentQuotientResolution q n ⟶
    (relativeFunctorCore q (join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) :=
  equivalencePathReplacementProjection _

/-- 二脚を同時に保持する一つの全比較であり、両脚の比較を独立に選ばない。 -/
def simplexAttachmentQuotientResolutionIso :
    FunctorIso (simplexAttachmentQuotientResolutionSource q n ≫
      simplexAttachmentQuotientComparison q n) (simplexAttachmentQuotientResolutionMap q n) :=
  equivalencePathReplacementFunctorIso _

/-- 実比較の全写像空間の同値から、比較経路を保持する全境界の充填を証明する。 -/
instance simplexAttachmentQuotientResolutionMap_trivialKanFibration :
    TrivialKanFibration (simplexAttachmentQuotientResolutionMap q n) := by
  have he := simplexAttachmentQuotientComparison_isQCatEquivalence q n
  exact he.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
    he.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective

/-- 指定部分族を厳密に保持し、同じ境界・商図式上の比較の全族を延長する。 -/
lemma exists_relative_simplexAttachmentQuotientFamily {P Q : SSet.{u}}
    (i : P ⟶ Q) [Mono i] (a : P ⟶ simplexAttachmentQuotientResolution q n)
    (b : Q ⟶ simplexAttachmentQuotientPullback q n)
    (ha : a ≫ simplexAttachmentQuotientResolutionMap q n = i ≫ b) :
    ∃ F : Q ⟶ simplexAttachmentQuotientResolution q n,
      i ≫ F = a ∧ F ≫ simplexAttachmentQuotientResolutionMap q n = b := by
  have := TrivialKanFibration.mem (p := simplexAttachmentQuotientResolutionMap q n)
    i inferInstance
  have sq : CommSq a i (simplexAttachmentQuotientResolutionMap q n) b := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.Derived.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_relative_simplexAttachmentQuotientFamily := _root_.SerrePositivity.InfinityCategories.Derived.Localization.exists_relative_simplexAttachmentQuotientFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentCoreRestriction_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentCoreRestriction_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentCoreRestriction_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison_boundary := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientComparison_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison_quotient := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientComparison_quotient

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullback (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullback := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullback

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullbackProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullbackProjection := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullbackProjection

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullbackProjection_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullbackProjection_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullbackProjection_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullback_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullback_quasicategory := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullback_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolution (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolution := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolution

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionIso := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionMap := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionMap_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionMap_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionMap_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionSource := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientResolutionSource

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullback._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentQuotientPullback._proof_1
