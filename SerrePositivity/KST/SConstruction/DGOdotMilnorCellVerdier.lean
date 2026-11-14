module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCellNativeValue
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCompletion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientThickLocalization

/-!
概要：実 S 零化面と同じ thick 平坦核・cell gluing・resolved 商の native 列を固定する。
方針：D の同じ包含・射影・thick 局所化を Sp 正本の列へ特殊化する。
規約：元対角始域の native 列は不変とし、この列は実零化面の認証用に使う。
使われ方：d④ の同じ固定 ν 辺と完備化付き実面の照合。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants

open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "T" => DGCategoryCellResolution.Source R (B)
local notation "P" => dgQuotientImage R
  (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B) (P)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (B) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (T) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (B)

/-- 概要：同じ thick 平坦核の native 安定圏。
方針：D の実核の安定性を使用する。規約：対象集合は不変。
使われ方：零化面用の実列の左端。 -/
def dgOdotMilnorCellKernelCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (K)
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel_isStable R (B) (P)

/-- 概要：同じ cell gluing の native 安定圏。
方針：実 cell 分解の前三角性を使用する。規約：元の商射影の始域を保つ。
使われ方：零化面用の実列の中央。 -/
def dgOdotMilnorCellMiddleCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (T)
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (T)

/-- 概要：同じ平坦核包含の完全射。
方針：D の full 核包含の完全性を使用する。規約：元の包含そのもの。
使われ方：零化面用の実列の左辺。 -/
def dgOdotMilnorCellKernelInclusion : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorCellKernelCategory R d)
    (dgOdotMilnorCellMiddleCategory R d) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (P))
  isExact := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion_isExactFunctor R (B) (P)

/-- 概要：同じ cell 商包含の完全射。
方針：同じ local K 平坦分解の射影を使用する。規約：native 商は変更しない。
使われ方：零化面用の実列の右辺。 -/
def dgOdotMilnorCellNativeProjection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgOdotMilnorCellMiddleCategory R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R (B) (P)
  isExact := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor R _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R (B) (P))

/-- 概要：実零化面と同じ二辺を持つ native Verdier 列。
方針：D の thick 核の零対象反映と同じ実局所化を使用する。
規約：Milnor 条件はこの核列には不要。使われ方：同じ実面の完備化認証。 -/
def dgOdotMilnorCellNativeSequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u + 1} where
  left := dgOdotMilnorCellKernelCategory R d
  middle := dgOdotMilnorCellMiddleCategory R d
  right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorNativeResolvedQuotient R d
  inclusion := dgOdotMilnorCellKernelInclusion R d
  projection := dgOdotMilnorCellNativeProjection R d
  isVerdier := {
    fullyFaithful := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion_isFullyFaithful R (B) (P)
    kernel := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_zero_iff_thickEssentialImage R (B) (P)
    quotient := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_isThickLocalization R (B) (P) }

/-- 概要：同じ核列と実 c・hc の完備化付き Cat^perf 列。
方針：構成済みの native 完備性と D-21 の特殊化を使用する。
規約：元対角始域の列とは別の同じ実零化面用の列。使われ方：ofSquare 認証。 -/
def dgOdotMilnorCellPerfectSequence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    PerfectVerdierSequence.{u + 1} where
  verdier := dgOdotMilnorCellNativeSequence R d
  left_complete := dgOdotMilnorSourceKernel_complete R d h
  middle_complete := dgOdotMilnorCellMiddle_complete R d
  right := dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
  completion := dgOdotMilnorCompletion R d
  isCompletion := dgOdotMilnorCompletion_isIdempotentCompletion R d

end SerrePositivity.KST.SConstruction
