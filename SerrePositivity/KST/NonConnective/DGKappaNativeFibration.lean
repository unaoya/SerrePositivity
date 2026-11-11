module
public import SerrePositivity.KST.NonConnective.DGKappaNativeVerdier
public import SerrePositivity.KST.Fibration.RelativeQuotientFiberComparison
public import SerrePositivity.KST.Fibration.QuotientSKernelPositiveStages

/-!
概要：同じ完備化前の実 Verdier 列を、元の相対 S• fiber 比較へ代入する。
方針：元の実核・包含・商射を保持し、相対比較と正段の商実現比較を分離する。
規約：商 fiber 側は既存の正段比較に条件付き。共終性と固定 ν の認証を混同しない。
使われ方：採用経路の K-6 c5 の完備化前の fibration と、K-7 c5・d3 への入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Fibration
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実核の core S• 実現は、同じ相対 S• 射の指定 fiber と局所化で同型。
方針：構成済みの完備化前の native Verdier 認証を元の相対 fibration へ代入する。
規約：I に条件付き。正段の商比較や共終性はこの相対比較には要求しない。
使われ方：K-6 c5 の完備化前の相対構成を元の実核へ接続する。 -/
def dgKappaNativeRelativeSFiberIso :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj
      (sInputModel (dgKappaNativeKernelCategory R D I))) ≅
    AnodyneHomotopy.anodyneQ.obj
      (relativeSFibrationFiber (dgKappaNative_isVerdierSequence R D I)) :=
  relativeSFibrationFiberIso (dgKappaNative_isVerdierSequence R D I)

set_option maxHeartbeats 800000 in
-- 同じ実 dg 核・平坦源を代入した依存 fiber 模型の型照合を完了する。
/-- 概要：同じ相対 fiber 比較は、D-9 の元の実核包含の実現射を回収する。
方針：元の相対 fibration の射影回収をそのまま代入する。
規約：実包含の辺や実現射を選び直さない。
使われ方：元の実核から中央項への脚の厳密な照合。 -/
theorem dgKappaNativeRelativeSFiberIso_projection :
    (dgKappaNativeRelativeSFiberIso R D I).hom ≫ AnodyneHomotopy.anodyneQ.map
      (relativeSFibrationFiberProjection (dgKappaNative_isVerdierSequence R D I)) =
    AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map
      (coreSExactMap (dgKappaNativeKernelInclusion R D I))) :=
  relativeSFibrationFiberIso_hom_projection (dgKappaNative_isVerdierSequence R D I)

variable (hstage : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
  (relativeSQuotientMap (dgKappaNativeQuotient R D I) (n + 1))))

/-- 概要：正段の商実現比較に条件付きで、同じ実商射の fiber と元の実核実現を比較する。
方針：零段の既証明比較を補い、同じ相対 fiber 比較に元の商比較を続ける。
規約：正段比較の証明・存在は主張しない。Perf 完備化の共終性は別の仮定引数で扱う。
使われ方：K-6 c5 の完備化前の実商への fibration。 -/
def dgKappaNativeQuotientSFiberIso :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj
      (sInputModel (dgKappaNativeKernelCategory R D I))) ≅
    AnodyneHomotopy.anodyneQ.obj
      (quotientSFibrationFiber (dgKappaNative_isVerdierSequence R D I)) :=
  quotientSFibrationFiberIsoOfComparison (dgKappaNative_isVerdierSequence R D I)
    (relativeSQuotientRealization_localized_isIso_of_positive_stages
      (dgKappaNativeQuotient R D I) hstage)

set_option maxHeartbeats 800000 in
-- 同じ元の実包含と正段比較を含む依存 fiber 模型の型照合を完了する。
/-- 概要：正段比較に条件付きの同じ商 fiber 比較も、元の実核包含の実現射を回収する。
方針：元の商 fiber 比較の射影回収を同じ正段比較へ適用する。
規約：完備化後の包含へ読み替えない。
使われ方：K-7 の同じ cone 上の構造射へ渡す元の包含脚。 -/
theorem dgKappaNativeQuotientSFiberIso_projection :
    (dgKappaNativeQuotientSFiberIso R D I hstage).hom ≫ AnodyneHomotopy.anodyneQ.map
      (quotientSFibrationFiberProjection (dgKappaNative_isVerdierSequence R D I)) =
    AnodyneHomotopy.anodyneQ.map (simplicialDiagonalFunctor.map
      (coreSExactMap (dgKappaNativeKernelInclusion R D I))) :=
  quotientSFibrationFiberIsoOfComparison_hom_projection (dgKappaNative_isVerdierSequence R D I)
    (relativeSQuotientRealization_localized_isIso_of_positive_stages
      (dgKappaNativeQuotient R D I) hstage)

include hstage in
/-- 概要：同じ正段比較に条件付きで、完備化前の実商の Ex∞ 核四角形は引き戻し。
方針：同じ元の商比較だけを既存の商核四角形へ代入する。
規約：元の native Verdier 全四角形との比較や Sp 引き戻し性は結論しない。
使われ方：K-6 c4 の全二胞体比較と c5 の商実現比較の接続先。 -/
theorem dgKappaNativeQuotientSKernel_isPullback :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientSKernelInfinitySquare (dgKappaNativeKernelInclusion R D I)
      (dgKappaNativeQuotient R D I)) :=
  quotientSKernelInfinitySquare_isPullback_of_positive_stages _ _
    (dgKappaNative_isVerdierSequence R D I) hstage

end SerrePositivity.KST.NonConnective
