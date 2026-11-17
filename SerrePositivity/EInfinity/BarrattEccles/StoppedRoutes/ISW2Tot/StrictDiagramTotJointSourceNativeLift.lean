module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ContinuousLeftFibrationAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningBaseChange

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の全要素からnative Homへの同じ全写像を、元の置換単位を固定して延長する。
方針：同じnative Homのleft fibrationと既存の相対left-anodyne延長を使う。
規約：元の射影・置換・単位を保つ。延長の同値性はまだ主張しない。
使われ方：R03dの同じ底上の比較射の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]
local instance jointSourceNativeLiftModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointSourceNativeLiftFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 同じ正本Homの元の二変数入力への射影は、同じleft fibrationの引き戻し。 -/
lemma strictBETotJointNativeHomProjection_leftFibration :
    LeftFibration (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A) :=
  ⟨leftFibrations.pullback_snd (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A) (LeftFibration.mem (p := twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))⟩
attribute [local instance] _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection_leftFibration

/-- 元の全要素からの同じnative Hom写像を、元の同じ置換単位を固定して延長する。 -/
theorem exists_strictBETotJointSourceNativeLift :
    let P : Over (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A)) :=
      Over.mk (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A))
    let R := (continuousLeftFibrationReplacement (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).obj P
    ∃ f : R.left ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomTotalSpace A,
      f ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).app P).left ≫ f =
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeHomMap A := by
  dsimp only
  apply exists_relativeFunctorExtension_of_leftAnodyne
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A)
    ((continuousLeftFibrationReplacement (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).obj
      (Over.mk (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A)))).hom
    ((continuousLeftFibrationReplacementUnit (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).app _).left
    (continuousLeftFibrationReplacementUnit_leftAnodyne _)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeHomMap A)
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeHomMap_projection]
  exact ((continuousLeftFibrationReplacementUnit (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).app
    (Over.mk (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A)))).w.symm
/-- 同じnative Hom全空間の分類は、元の二変数native Hom図式と全関手同型。 -/
def strictBETotJointNativeHomClassificationIso :
    FunctorIso (leftStraighteningInfinityDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomCoherent A) := by
  have : Quasicategory ((_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) := quasicategory_tensor _ _
  exact (leftStraighteningInfinityDiagram_baseChangeIso
    (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A)).symm
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
