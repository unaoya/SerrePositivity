module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointPairingBaseComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquareExactIso

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の全pairingを、同じ元の二変数native入力の上で厳密に可換にする。
方針：元の全端点比較を指定pathとして、既存のleft-fibrationの相対path補正を使う。
規約：同じ元の全端点比較への投影の等式を保持する。比較の同値性はまだ主張しない。
使われ方：元の全要素から同じ底上のnative Homの全空間への射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable (A : Type u) [CommRing A]
local instance jointPairingCorrectionModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointPairingCorrectionFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance jointPairingCorrectionBase : Quasicategory ((_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) :=
  quasicategory_tensor _ _

/-- 元の全端点比較の同じ逆を、元のpairingの同じ射影へ接続する。 -/
def strictBETotJointSourcePairingBasePathIso :
    FunctorIso
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) :=
  functorIsoOfEq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBaseIso A).symm rfl
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_projection A).symm

/-- 元の全端点比較を指定した、同じpairingの相対path補正。 -/
def strictBETotJointSourcePairingCorrection :
    PathCorrectedFunctorSquare (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A)
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingBasePathIso A) :=
  pathCorrectedFunctorSquare _ (leftFibration_equivalenceLifting _)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A)
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingBasePathIso A)

/-- 元のpairingを同じ二変数native入力の上へ戻した全写像。 -/
def strictBETotJointSourceCorrectedPairing :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶ TwistedArrow (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingCorrection A).map

/-- 同じ補正後のpairingの射影は、元の二変数native入力へ厳密に一致。 -/
theorem strictBETotJointSourceCorrectedPairing_projection :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A ≫ twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) =
      nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingCorrection A).comm

/-- 元の指定pathに沿う、補正後のpairingと元のpairingの同じ全比較。 -/
def strictBETotJointSourceCorrectedPairingIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingCorrection A).exactComponentIso

/-- 同じ全比較の射影は、元の端点比較自身を同じ厳密な射影等式で移したもの。 -/
theorem strictBETotJointSourceCorrectedPairingIso_postcomp :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) =
      eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingBasePathIso A :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairingCorrection A).exactComponentIso_postcomp

/-- 元の二変数native入力で引き戻した正本Homの全空間。 -/
def strictBETotJointNativeHomTotalSpace : SSet.{u+1} :=
  pullback (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A)

/-- 同じ正本Homの全空間から元の二変数の底への射影。 -/
def strictBETotJointNativeHomProjection :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomTotalSpace A ⟶ nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :=
  pullback.snd _ _

/-- 元の全要素から、同じ元の底上のnative Homの全空間への実際の全写像。 -/
def strictBETotJointSourceNativeHomMap :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomTotalSpace A :=
  pullback.lift (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A)
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_projection A)

/-- 同じ全写像の元の底への射影の厳密な等式。 -/
theorem strictBETotJointSourceNativeHomMap_projection :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeHomMap A ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A =
      nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A) := pullback.lift_snd _ _ _

/-- 同じ全写像は元の指定pathで補正されたpairingをそのまま回収。 -/
theorem strictBETotJointSourceNativeHomMap_pairing :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeHomMap A ≫
      pullback.fst (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A) =
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A := pullback.lift_fst _ _ _
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
