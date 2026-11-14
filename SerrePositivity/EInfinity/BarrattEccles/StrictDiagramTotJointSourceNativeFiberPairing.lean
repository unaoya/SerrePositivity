module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberPullback

/-!
概要：元のnative fiber射を引き戻しのfiber同型で元のtwisted-arrow fiberへ戻す。
方針：同じfiber包含と元のpullbackの第一射影の厳密な等式を合成する。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance jointNativeFiberPairingModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeFiberPairingFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩


/-- 指定された同じfiber射を、同じ引き戻しの第一射影のfiberへ運ぶ。 -/
def strictBETotJointSourceNativeTwistedFiberMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P)) :=
  strictBETotJointSourceNativeFiberMap A P ≫
    (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
      (strictBETotJointNativeHomInput A) (nerveVertex P)).hom

/-- 包含後の元のnative fiber射は、同じ元の全要素上の写像への制限。 -/
theorem strictBETotJointSourceNativeFiberMap_ι (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceNativeFiberMap A P ≫
      vertexFiberι (strictBETotJointNativeHomProjection A) (nerveVertex P) =
        simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
          strictBETotJointSourceNativeHomMap A := by
  unfold strictBETotJointSourceNativeFiberMap simplicialElementsFiberMap
  rw [vertexFiberLift_ι]

/-- 同じ第一射影のfiberへ戻して包含すると、同じ補正済pairingへの制限そのもの。 -/
theorem strictBETotJointSourceNativeTwistedFiberMap_ι (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceNativeTwistedFiberMap A P ≫
      vertexFiberι (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P)) =
      simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A := by
  rw [strictBETotJointSourceNativeTwistedFiberMap, Category.assoc,
    vertexFiberPullbackIso_hom_ι, ← Category.assoc]
  change (strictBETotJointSourceNativeFiberMap A P ≫
    vertexFiberι (strictBETotJointNativeHomProjection A) (nerveVertex P)) ≫
      pullback.fst (twistedArrowProjection (CAlg_R A)) (strictBETotJointNativeHomInput A) = _
  rw [strictBETotJointSourceNativeFiberMap_ι, Category.assoc,
    strictBETotJointSourceNativeHomMap_pairing]
end SerrePositivity.EInfinity.BarrattEccles
