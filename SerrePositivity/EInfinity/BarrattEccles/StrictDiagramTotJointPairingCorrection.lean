module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingBaseComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.PathCorrectedSquareExactIso

/-!
概要：元の全pairingを、同じ元の二変数native入力の上で厳密に可換にする。
方針：元の全端点比較を指定pathとして、既存のleft-fibrationの相対path補正を使う。
規約：同じ元の全端点比較への投影の等式を保持する。比較の同値性はまだ主張しない。
使われ方：元の全要素から同じ底上のnative Homの全空間への射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet MonoidalCategory Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
variable (A : Type u) [CommRing A]
local instance jointPairingCorrectionModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointPairingCorrectionFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointPairingCorrectionBase : Quasicategory ((CAlg_R A).op ⊗ CAlg_R A) :=
  quasicategory_tensor _ _

/-- 元の全端点比較の同じ逆を、元のpairingの同じ射影へ接続する。 -/
def strictBETotJointSourcePairingBasePathIso :
    FunctorIso
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
      (strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (CAlg_R A)) :=
  functorIsoOfEq (strictBETotJointSourceNativePairingBaseIso A).symm rfl
    (strictBETotJointSourceNativePairing_projection A).symm

/-- 元の全端点比較を指定した、同じpairingの相対path補正。 -/
def strictBETotJointSourcePairingCorrection :
    PathCorrectedFunctorSquare (twistedArrowProjection (CAlg_R A))
      (strictBETotJointSourceNativePairing A)
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
      (strictBETotJointSourcePairingBasePathIso A) :=
  pathCorrectedFunctorSquare _ (leftFibration_equivalenceLifting _)
    (strictBETotJointSourceNativePairing A)
    (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A)
    (strictBETotJointSourcePairingBasePathIso A)

/-- 元のpairingを同じ二変数native入力の上へ戻した全写像。 -/
def strictBETotJointSourceCorrectedPairing :
    nerve (StrictBETotJointSourceElements A) ⟶ TwistedArrow (CAlg_R A) :=
  (strictBETotJointSourcePairingCorrection A).map

/-- 同じ補正後のpairingの射影は、元の二変数native入力へ厳密に一致。 -/
theorem strictBETotJointSourceCorrectedPairing_projection :
    strictBETotJointSourceCorrectedPairing A ≫ twistedArrowProjection (CAlg_R A) =
      nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A :=
  (strictBETotJointSourcePairingCorrection A).comm

/-- 元の指定pathに沿う、補正後のpairingと元のpairingの同じ全比較。 -/
def strictBETotJointSourceCorrectedPairingIso :
    FunctorIso (strictBETotJointSourceCorrectedPairing A) (strictBETotJointSourceNativePairing A) :=
  (strictBETotJointSourcePairingCorrection A).exactComponentIso

/-- 同じ全比較の射影は、元の端点比較自身を同じ厳密な射影等式で移したもの。 -/
theorem strictBETotJointSourceCorrectedPairingIso_postcomp :
    (strictBETotJointSourceCorrectedPairingIso A).postcomp (twistedArrowProjection (CAlg_R A)) =
      eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A :=
  (strictBETotJointSourcePairingCorrection A).exactComponentIso_postcomp

/-- 元の二変数native入力で引き戻した正本Homの全空間。 -/
def strictBETotJointNativeHomTotalSpace : SSet.{u+1} :=
  pullback (twistedArrowProjection (CAlg_R A)) (strictBETotJointNativeHomInput A)

/-- 同じ正本Homの全空間から元の二変数の底への射影。 -/
def strictBETotJointNativeHomProjection :
    strictBETotJointNativeHomTotalSpace A ⟶ nerve (strictBETotJointHomIndex A) :=
  pullback.snd _ _

/-- 元の全要素から、同じ元の底上のnative Homの全空間への実際の全写像。 -/
def strictBETotJointSourceNativeHomMap :
    nerve (StrictBETotJointSourceElements A) ⟶ strictBETotJointNativeHomTotalSpace A :=
  pullback.lift (strictBETotJointSourceCorrectedPairing A)
    (nerveMap (strictBETotJointSourceElementsProjection A))
    (strictBETotJointSourceCorrectedPairing_projection A)

/-- 同じ全写像の元の底への射影の厳密な等式。 -/
theorem strictBETotJointSourceNativeHomMap_projection :
    strictBETotJointSourceNativeHomMap A ≫ strictBETotJointNativeHomProjection A =
      nerveMap (strictBETotJointSourceElementsProjection A) := pullback.lift_snd _ _ _

/-- 同じ全写像は元の指定pathで補正されたpairingをそのまま回収。 -/
theorem strictBETotJointSourceNativeHomMap_pairing :
    strictBETotJointSourceNativeHomMap A ≫
      pullback.fst (twistedArrowProjection (CAlg_R A)) (strictBETotJointNativeHomInput A) =
        strictBETotJointSourceCorrectedPairing A := pullback.lift_fst _ _ _
end SerrePositivity.EInfinity.BarrattEccles
