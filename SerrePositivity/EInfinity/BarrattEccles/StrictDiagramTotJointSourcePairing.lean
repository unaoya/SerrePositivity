module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceElements
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotModelSource
public import SerrePositivity.EInfinity.FrameHom.LiftedSourceFramePairing

/-!
概要：元のBEの全source-frameの射を、同じモデル源のnative twisted arrowへ送る。
方針：同じ実pairingに元のモデル源のedgewise写像を合成し、射影の自然性を使う。
規約：元の両端と全高次を保つ。augmentationの逆による始域の変更は別。
使われ方：元の全要素分類から正本Hom∞へのR03dの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet MonoidalCategory
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable (A : Type u) [CommRing A]
local instance jointSourcePairingModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourcePairingFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全source-frameの実射の、同じ持ち上げた通常圏での全pairing。 -/
def strictBETotJointSourcePairing :
    nerve (StrictBETotJointSourceElements A) ⟶
      TwistedArrow (nerve (AsSmall.{u+1} (operad A).Algebra)) :=
  FrameHom.liftedSourceFramePairing (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A))

/-- 元の全pairingを、同じ元のモデル源でnative twisted arrowへ送る。 -/
def strictBETotJointSourceNativePairing :
    nerve (StrictBETotJointSourceElements A) ⟶ TwistedArrow (CAlg_R A) :=
  strictBETotJointSourcePairing A ≫ edgewiseSubdivisionMap (strictBETotModelSource A)

/-- 元の全pairingの両端を、同じ元のモデル源で送ったnativeの底。 -/
def strictBETotJointSourceNativePairingBase :
    nerve (StrictBETotJointSourceElements A) ⟶ (CAlg_R A).op ⊗ CAlg_R A :=
  CartesianMonoidalCategory.lift
    (nerveMap (FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A))) ≫
      (nerveOppositeIso (C := AsSmall.{u+1} (operad A).Algebra)).inv)
    (nerveMap (FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)))) ≫
    (SSet.opFunctor.map (strictBETotModelSource A) ⊗ₘ strictBETotModelSource A)

/-- 同じnative pairingは元の全実射の同じ両端を厳密に保つ。 -/
theorem strictBETotJointSourceNativePairing_projection :
    strictBETotJointSourceNativePairing A ≫ twistedArrowProjection (CAlg_R A) =
      strictBETotJointSourceNativePairingBase A := by
  rw [strictBETotJointSourceNativePairing, Category.assoc,
    twistedArrowProjection_naturality, ← Category.assoc]
  change (FrameHom.liftedSourceFramePairing (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A)) ≫ _) ≫ _ = _
  rw [FrameHom.liftedSourceFramePairing_projection]
  rfl
end SerrePositivity.EInfinity.BarrattEccles
