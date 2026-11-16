module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange

/-!
概要：元の全要素からnative Homへの同じ全写像を、元の置換単位を固定して延長する。
方針：同じnative Homのleft fibrationと既存の相対left-anodyne延長を使う。
規約：元の射影・置換・単位を保つ。延長の同値性はまだ主張しない。
使われ方：R03dの同じ底上の比較射の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits MonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]
local instance jointSourceNativeLiftModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceNativeLiftFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じ正本Homの元の二変数入力への射影は、同じleft fibrationの引き戻し。 -/
lemma strictBETotJointNativeHomProjection_leftFibration :
    LeftFibration (strictBETotJointNativeHomProjection A) :=
  ⟨leftFibrations.pullback_snd (twistedArrowProjection (CAlg_R A))
    (strictBETotJointNativeHomInput A) (LeftFibration.mem (p := twistedArrowProjection (CAlg_R A)))⟩
attribute [local instance] strictBETotJointNativeHomProjection_leftFibration

/-- 元の全要素からの同じnative Hom写像を、元の同じ置換単位を固定して延長する。 -/
theorem exists_strictBETotJointSourceNativeLift :
    let P : Over (nerve (strictBETotJointHomIndex A)) :=
      Over.mk (nerveMap (strictBETotJointSourceElementsProjection A))
    let R := (continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj P
    ∃ f : R.left ⟶ strictBETotJointNativeHomTotalSpace A,
      f ≫ strictBETotJointNativeHomProjection A = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app P).left ≫ f =
        strictBETotJointSourceNativeHomMap A := by
  dsimp only
  apply exists_relativeFunctorExtension_of_leftAnodyne
    (strictBETotJointNativeHomProjection A)
    ((continuousLeftFibrationReplacement (nerve (strictBETotJointHomIndex A))).obj
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).hom
    ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app _).left
    (continuousLeftFibrationReplacementUnit_leftAnodyne _)
    (strictBETotJointSourceNativeHomMap A)
  rw [strictBETotJointSourceNativeHomMap_projection]
  exact ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
    (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).w.symm
/-- 同じnative Hom全空間の分類は、元の二変数native Hom図式と全関手同型。 -/
def strictBETotJointNativeHomClassificationIso :
    FunctorIso (leftStraighteningInfinityDiagram (strictBETotJointNativeHomProjection A))
      (strictBETotJointNativeHomCoherent A) := by
  have : Quasicategory ((CAlg_R A).op ⊗ CAlg_R A) := quasicategory_tensor _ _
  exact (leftStraighteningInfinityDiagram_baseChangeIso
    (twistedArrowProjection (CAlg_R A)) (strictBETotJointNativeHomInput A)).symm
end SerrePositivity.EInfinity.BarrattEccles
