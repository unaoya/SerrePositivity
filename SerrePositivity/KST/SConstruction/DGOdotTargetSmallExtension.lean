module
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallRepresentation
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionClosedFamily

/-! # 同じ小さい実模型での cone 比較の一回 Perf 延長
概要：元の cone 作用と元の End 比較の指定同型を、同じ一回 Perf 延長へ作用させる。
方針：元の入力 Hom end の閉同型と、既存の実延長の全 Hom 作用を使う。
規約：同じ小模型・元の成分を保持。使われ方：元の比較代数射との Perf 図式の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "CRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.left d)
local notation "DRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "gRaw" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "CL" => DGSmallPerfectArrowTarget R (A) (CRaw) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (DRaw) (gRaw)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (CRaw) (DRaw) (E) (L) (gRaw) (p) (q)
local notation "I" => dgOdotQuotientInput R d

local notation "zc" => dgSmallPerfectArrowTargetZero R (A) (CRaw) (L)
local notation "hc" => dgSmallPerfectArrowTargetZero_isZero R (A) (CRaw) (L)
local notation "b" => dgOdotInputRightPoint R d

local notation "J" => dgSmallPerfectSquareCornerInclusion R (A) (CRaw) (DRaw) (E)
  (L) (gRaw) (p) (q)

/-- 同じ小模型の二つの作用を、元の Hom end の dg 関手圏内で結ぶ閉同型。 -/
def dgOdotSmallConeInputIso :
    ForgetEnrichment.of (Complex R) (dgOdotConeSmallRepresentation R d) ≅
      ForgetEnrichment.of (Complex R) (dgOdotTargetSmallRepresentation R d) :=
  dgFunctorClosedIsoFromFamily R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
    (dgOdotConeSmallRepresentation R d) (dgOdotTargetSmallRepresentation R d)
    (fun _ => dgOdotTargetSmallPointIso R d) (dgOdotTargetSmallPointIso_naturality R d)

/-- 同じ入力閉同型の順射は、元の小模型の同じ三段比較を回収する。 -/
lemma dgOdotSmallConeInputIso_hom_eval (x : DGOdotQuotientEnd R d) :
    (dgFunctorEvaluationDG R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d) x).onClosed.map
      (dgOdotSmallConeInputIso R d).hom = (dgOdotTargetSmallPointIso R d).hom :=
  dgFunctorClosedHomFromFamily_eval R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
    (dgOdotConeSmallRepresentation R d) (dgOdotTargetSmallRepresentation R d) _ _ x

/-- 同じ入力閉同型の逆射も、元の小模型の同じ逆射を回収する。 -/
lemma dgOdotSmallConeInputIso_inv_eval (x : DGOdotQuotientEnd R d) :
    (dgFunctorEvaluationDG R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d) x).onClosed.map
      (dgOdotSmallConeInputIso R d).inv = (dgOdotTargetSmallPointIso R d).inv :=
  dgFunctorClosedHomFromFamily_eval R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
    (dgOdotTargetSmallRepresentation R d) (dgOdotConeSmallRepresentation R d) _ _ x

/-- 元の小模型内の同型を使う、同じ一回 Perf 延長の各実入力上の比較。 -/
def dgOdotSmallConePerfectAt (M : PerfectDGModule R (DGOdotQuotientEnd R d)) :
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
        (dgOdotConeSmallRepresentation R d)).obj M) ≅
    ForgetEnrichment.of (Complex R)
      ((perfectDGExtension R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
        (dgOdotTargetSmallRepresentation R d)).obj M) :=
  perfectDGExtensionClosedIsoFromFamilyAt R (DGOdotQuotientEnd R d)
    (DGOdotTargetSmallPerfect R d) (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d) M

/-- 同じ元の単位パラメータ比較の、実一回 Perf 延長。 -/
def dgOdotSmallConePerfectComparison :=
  perfectDGExtensionParameter R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
    (dgOdotSmallConeRepresentationComparison R d)

/-- 同じ元の逆比較の、実一回 Perf 延長。 -/
def dgOdotSmallConePerfectInverseComparison :=
  perfectDGExtensionParameter R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
    (dgOdotSmallConeRepresentationInverseComparison R d)

/-- 実入力上の同型の順射は、同じ全次数比較の元の延長成分。 -/
lemma dgOdotSmallConePerfectAt_hom (M : PerfectDGModule R (DGOdotQuotientEnd R d)) :
    ForgetEnrichment.homTo (Complex R) (dgOdotSmallConePerfectAt R d M).hom =
      (dgOdotSmallConePerfectComparison R d).app M :=
  perfectDGExtensionClosedIsoFromFamilyAt_hom R (DGOdotQuotientEnd R d)
    (DGOdotTargetSmallPerfect R d) (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d) M

/-- 実入力上の同型の逆射も、同じ元の逆比較の延長成分。 -/
lemma dgOdotSmallConePerfectAt_inv (M : PerfectDGModule R (DGOdotQuotientEnd R d)) :
    ForgetEnrichment.homTo (Complex R) (dgOdotSmallConePerfectAt R d M).inv =
      (dgOdotSmallConePerfectInverseComparison R d).app M :=
  perfectDGExtensionClosedIsoFromFamilyAt_inv R (DGOdotQuotientEnd R d)
    (DGOdotTargetSmallPerfect R d) (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d) M

/-- 同じ一回延長同型は、元の実 perfect 入力の全 Hom に関して自然。 -/
lemma dgOdotSmallConePerfectAt_naturality (X Y : PerfectDGModule R (DGOdotQuotientEnd R d)) :
    (perfectDGExtension R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
      (dgOdotConeSmallRepresentation R d)).map X Y ≫ eHomWhiskerLeft (Complex R) _
        (dgOdotSmallConePerfectAt R d Y).hom =
    (perfectDGExtension R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
      (dgOdotTargetSmallRepresentation R d)).map X Y ≫ eHomWhiskerRight (Complex R)
        (dgOdotSmallConePerfectAt R d X).hom _ :=
  perfectDGExtensionClosedIsoFromFamilyAt_naturality R (DGOdotQuotientEnd R d)
    (DGOdotTargetSmallPerfect R d) (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d) X Y

/-- 同じ元の入力比較に由来する、実一回 Perf 延長の閉零自然同型。 -/
def dgOdotSmallConePerfectClosedIso :
    (perfectDGExtension R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
      (dgOdotConeSmallRepresentation R d)).onClosed ≅
    (perfectDGExtension R (DGOdotQuotientEnd R d) (DGOdotTargetSmallPerfect R d)
      (dgOdotTargetSmallRepresentation R d)).onClosed :=
  perfectDGExtensionClosedIsoFromFamily R (DGOdotQuotientEnd R d)
    (DGOdotTargetSmallPerfect R d) (dgOdotConeSmallRepresentation R d)
    (dgOdotTargetSmallRepresentation R d) (fun _ => dgOdotTargetSmallPointIso R d)
    (dgOdotTargetSmallPointIso_naturality R d)

end SerrePositivity.KST.SConstruction
