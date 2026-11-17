module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceElements
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotModelSource
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LiftedSourceFramePairing

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBEの全source-frameの射を、同じモデル源のnative twisted arrowへ送る。
方針：同じ実pairingに元のモデル源のedgewise写像を合成し、射影の自然性を使う。
規約：元の両端と全高次を保つ。augmentationの逆による始域の変更は別。
使われ方：元の全要素分類から正本Hom∞へのR03dの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable (A : Type u) [CommRing A]
local instance jointSourcePairingModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointSourcePairingFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の全source-frameの実射の、同じ持ち上げた通常圏での全pairing。 -/
def strictBETotJointSourcePairing :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶
      TwistedArrow (nerve (AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFramePairing (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
    (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))

/-- 元の全pairingを、同じ元のモデル源でnative twisted arrowへ送る。 -/
def strictBETotJointSourceNativePairing :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶ TwistedArrow (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourcePairing A ≫ edgewiseSubdivisionMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)

/-- 元の全pairingの両端を、同じ元のモデル源で送ったnativeの底。 -/
def strictBETotJointSourceNativePairingBase :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶ (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op ⊗ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  CartesianMonoidalCategory.lift
    (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowDomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))) ≫
      (nerveOppositeIso (C := AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).inv)
    (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowCodomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)))) ≫
    (SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) ⊗ₘ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)

/-- 同じnative pairingは元の全実射の同じ両端を厳密に保つ。 -/
theorem strictBETotJointSourceNativePairing_projection :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairingBase A := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing, Category.assoc,
    twistedArrowProjection_naturality, ← Category.assoc]
  change (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFramePairing (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
    (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) ≫ _) ≫ _ = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFramePairing_projection]
  rfl
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
