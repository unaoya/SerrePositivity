module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeFunctorCoreRestriction
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {B C : SSet.{u}} [Quasicategory B] [Quasicategory C] (q : B ⟶ C) (n : ℕ)

instance simplexAttachmentCoreRestriction_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C)) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.coreMap_trivialKanFibration _

/-- 元の全商図式と、その境界を持つ元の相対図式の厳密 pullback。 -/
def simplexAttachmentQuotientPullback : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}))

def simplexAttachmentQuotientPullbackProjection : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback q n ⟶
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}) : SSet.{u}) :=
  pullback.snd _ _

instance simplexAttachmentQuotientPullbackProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection q n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

instance simplexAttachmentQuotientPullback_quasicategory :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback q n) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection q n)

/-- 同じ元の商射と同じ実制限射を二脚に持つ、指定された比較。 -/
def simplexAttachmentQuotientComparison :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback q n :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]))
    (relativeSimplexAttachmentRestriction q n) (relativeSimplexAttachmentQuotient_square q n).symm

omit [Quasicategory B] in
lemma simplexAttachmentQuotientComparison_quotient :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison q n ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) :=
  pullback.lift_fst _ _ _

omit [Quasicategory B] in
lemma simplexAttachmentQuotientComparison_boundary :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison q n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection q n =
      relativeSimplexAttachmentRestriction q n :=
  pullback.lift_snd _ _ _

/-- 同じ商比較を保持する実貼合せ工程の比較は、全 Hom の意味で同値。 -/
lemma simplexAttachmentQuotientComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison q n) := by
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection q n)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison q n ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection q n) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison_boundary]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _
  exact hp.cancel_right hc

/-- 全図式と商比較を記憶する可逆経路置換。 -/
def simplexAttachmentQuotientResolution : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison q n)

def simplexAttachmentQuotientResolutionMap : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolution q n ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback q n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap _

/-- 経路置換から、元の同じ全相対図式を回収する。 -/
def simplexAttachmentQuotientResolutionSource : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolution q n ⟶
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection _

/-- 二脚を同時に保持する一つの全比較であり、両脚の比較を独立に選ばない。 -/
def simplexAttachmentQuotientResolutionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionSource q n ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison q n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap q n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementFunctorIso _

/-- 実比較の全写像空間の同値から、比較経路を保持する全境界の充填を証明する。 -/
instance simplexAttachmentQuotientResolutionMap_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap q n) := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison_isQCatEquivalence q n
  exact he.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
    he.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective

/-- 指定部分族を厳密に保持し、同じ境界・商図式上の比較の全族を延長する。 -/
lemma exists_relative_simplexAttachmentQuotientFamily {P Q : SSet.{u}}
    (i : P ⟶ Q) [Mono i] (a : P ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolution q n)
    (b : Q ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback q n)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap q n = i ≫ b) :
    ∃ F : Q ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolution q n,
      i ≫ F = a ∧ F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap q n = b := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap q n)
    i inferInstance
  have sq : CommSq a i (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap q n) b := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_relative_simplexAttachmentQuotientFamily := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.exists_relative_simplexAttachmentQuotientFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentCoreRestriction_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentCoreRestriction_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentCoreRestriction_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison_boundary := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison_quotient := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison_quotient

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullbackProjection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullbackProjection_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullbackProjection_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullback_quasicategory := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback_quasicategory

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolution (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolution := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolution

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionMap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap_trivialKanFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionMap_trivialKanFibration := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionMap_trivialKanFibration

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionSource (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientResolutionSource := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientResolutionSource

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexAttachmentQuotientPullback._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentQuotientPullback._proof_1
