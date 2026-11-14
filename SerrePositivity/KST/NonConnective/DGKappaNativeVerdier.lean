module
public import SerrePositivity.KST.NonConnective.DGKappaNativeKernelThick
public import SerrePositivity.KST.NonConnective.DGKappaNativeConeResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotients.DGQuotientLocalization
public import SerrePositivity.KST.LocalizingInvariants.VerdierPresentation

/-!
概要：D-9 の同じ完備化前の実核・平坦源・実商を、Sp の Verdier 列認証へ接続する。
方針：同じ実核の本質像判定と D 正本の実 Verdier 辺の局所化を使う。
規約：同じ I に条件付き。固定 ν の Perf 完備化後の認証とは区別する。
使われ方：K-6 c5 の完備化前の連結 fibration と、K-7 の同じ cone 上の共終性経路。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "B" => DGCategoryCellResolution.Source R (DGKappaCone R D I)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)

local instance nativeVerdierFlatStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (B)) :=
  (dgKappaNativeResolvedCone R D I).stable
local instance nativeVerdierKernelStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStable R (DGKappaCone R D I)
    (dgKappaConePerfectObjects R D I)
local instance nativeVerdierSuspensionStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKappaSuspensionInfinity R D I) :=
  dgKappaSuspensionInfinity_isStable R D I

/-- 概要：同じ D-9 実小核の native 安定値。
方針：元の実包含の始域と D 正本の安定性を束ねる。
規約：Perf 完備化へ置換しない。
使われ方：完備化前の連結 fibration の左項。 -/
def dgKappaNativeKernelCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I), inferInstance,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStable R (DGKappaCone R D I)
      (dgKappaConePerfectObjects R D I)⟩

/-- 概要：同じ実平坦源の native 安定値。
方針：構成済みの同じ native 安定模型を束ね直す。
規約：元の増大・商射を変更しない。
使われ方：完備化前の連結 fibration の中央項。 -/
def dgKappaNativeConeCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  ⟨(dgKappaNativeResolvedCone R D I).carrier, inferInstance,
    (dgKappaNativeResolvedCone R D I).stable⟩

/-- 概要：同じ完備化前の実平坦商の native 安定値。
方針：D 正本の元の実商とその安定性を保持する。
規約：元の固定 ν の Perf 値との同一視はしない。
使われ方：完備化前の連結 fibration の右項。 -/
def dgKappaNativeSuspensionCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} :=
  ⟨dgKappaSuspensionInfinity R D I, inferInstance, dgKappaSuspensionInfinity_isStable R D I⟩

/-- 概要：同じ実小核の元の厳密 dg 包含を完全射として保持する。
方針：D-9 の native Verdier 列の包含完全性を使う。
規約：元の全単体写像を保持する。
使われ方：完備化前の Sp Verdier 認証への代入。 -/
def dgKappaNativeKernelInclusion :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKappaNativeKernelCategory R D I) (dgKappaNativeConeCategory R D I) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelInputMap R D I).down
  isExact := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStableVerdierSequence R
    (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)).inclusionExact

/-- 概要：同じ実平坦源から同じ実商への元の商包含を完全射として保持する。
方針：D-9 の native Verdier 列の商完全性を使う。
規約：元の全一単体を別の選択へ置換しない。
使われ方：完備化前の Sp Verdier 認証への代入。 -/
def dgKappaNativeQuotient :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgKappaNativeConeCategory R D I) (dgKappaNativeSuspensionCategory R D I) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedSuspensionInputMap R D I).down
  isExact := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFlatKernel_isStableVerdierSequence R
    (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)).quotientExact

/-- 概要：同じ元の実核の cofiber 辺は、D 正本の元の実 Verdier 辺と一致する。
方針：同じ本質像が元の native 安定閉包であることを辺の定義へ代入する。
規約：局所化の同種 API は新設せず、元の二つの辺集合を照合するだけ。
使われ方：完備化前の Sp 認証へ D 正本の局所化を渡す。 -/
theorem dgKappaNativeVerdierEdges_eq :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgKappaNativeKernelInclusion R D I)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges R (B) (P) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges
  congr 1
  ext b
  exact dgKappaNativeKernel_image_iff R D I b

/-- 概要：同じ実核・平坦源・実商は、完備化前の Sp Verdier 列をなす。
方針：元の kernel 判定と辺集合の一致を、D 正本の実局所化へ接続する。
規約：同じ I に条件付き。固定 ν の完備化後の Verdier 列は結論しない。
使われ方：K-6 c5 の完備化前の連結 fibration。 -/
theorem dgKappaNative_isVerdierSequence :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence (dgKappaNativeKernelInclusion R D I) (dgKappaNativeQuotient R D I) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
  refine ⟨?_, ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (B)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (B) (P))
  · intro b
    exact dgKappaNativeProjection_zero_iff_kernelImage R D I b
  · rw [dgKappaNativeVerdierEdges_eq]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isLocalization R (B) (P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))

/-- 概要：同じ完備化前の実核・平坦源・実商と元の二射を、Sp の元の列に束ねる。
方針：構成済みの同じ三値・完全射・Verdier 認証を保持する。
規約：固定 ν の Perf 完備化後の列へ置換しない。
使われ方：完備化前の連結 fibration の指定四角形への受け渡し。 -/
def dgKappaNativeVerdierSequence : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{max (u + 1) v} where
  left := dgKappaNativeKernelCategory R D I
  middle := dgKappaNativeConeCategory R D I
  right := dgKappaNativeSuspensionCategory R D I
  inclusion := dgKappaNativeKernelInclusion R D I
  projection := dgKappaNativeQuotient R D I
  isVerdier := dgKappaNative_isVerdierSequence R D I

/-- 概要：同じ元の二射を全一単体として保つ、完備化前の native Verdier 四角形。
方針：Sp 正本の同じ列の提示構成を利用する。
規約：零角付き提示の選択は保持する。固定 S 内の既存の条件付き屋根を変更しない。
使われ方：K-6 c4・c5 の同じ native 全四角形比較の利用側。 -/
def dgKappaNativeVerdierDiagram : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{max (u + 1) v} :=
  (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierSequence.presentation (dgKappaNativeVerdierSequence R D I))

/-- 概要：同じ native 四角形の包含辺は、D-9 の同じ実包含の全一単体。
方針：元の Sp 提示の包含辺回収を使う。
規約：ホモトピー類だけで代用しない。
使われ方：K-6 c4 の同じ native 境界照合。 -/
theorem dgKappaNativeVerdierDiagram_inclusion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (dgKappaNativeVerdierDiagram R D I).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeKernelInclusion R D I)).edge :=
  (dgKappaNativeVerdierDiagram R D I).bottom_edge

/-- 概要：同じ native 四角形の商辺は、元の実平坦商包含の全一単体。
方針：元の Sp 提示の商辺回収を使う。
規約：完備化後の射へ読み替えない。
使われ方：K-6 c4・c5 の同じ元の商射影の照合。 -/
theorem dgKappaNativeVerdierDiagram_quotient :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (dgKappaNativeVerdierDiagram R D I).square =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeQuotient R D I)).edge :=
  (dgKappaNativeVerdierDiagram R D I).right_edge

end SerrePositivity.KST.NonConnective
