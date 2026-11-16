module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeOppositeFiber
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointHomInputVertex
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofEndpointTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomPinchedComparison
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.OppositeWeakHomotopyReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite

/-!
概要：元のnative fiber射を、元の同じ両端のpinched Homへ運ぶ。
方針：元の入力頂点の等式でfiberを合わせ、既存のtwisted・pinched比較を合成する。
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
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
local instance jointNativePinchedModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativePinchedFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩



attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元のnative fiberの反転を、同じ元の両端のpinched Homへ送る比較同値。 -/
def strictBETotJointNativeFiberPinchedEquivalence (P : strictBETotJointHomIndex A) :
    QCatEquivalence
      (vertexFiber (twistedArrowProjection (CAlg_R A))
        ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))).op
      (Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))) :=
  (qCatEquivalenceOfIso (SSet.opFunctor.mapIso (eqToIso
    (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
      (strictBETotJointNativeHomInput_model_vertex A P))))).trans
        (twistedArrowHomOppositePinchedEquivalence _ _)

/-- 元のnative射自身を、同じ元の両端の基準roofと同じ標的へ送る。 -/
def strictBETotJointSourceNativePinchedMap (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))) :=
  strictBETotJointSourceNativeOppositeFiberMap A P ≫
    (strictBETotJointNativeFiberPinchedEquivalence A P).hom

/-- 同じpinched Homへ運んだ実射の弱同値性は、元のnative fiber射自身と同値。 -/
theorem strictBETotJointSourceNativePinchedMap_weak_iff_original
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceNativePinchedMap A P) ↔
      IsWeakHomotopyEquivalence (strictBETotJointSourceNativeFiberMap A P) := by
  have he := (strictBETotJointNativeFiberPinchedEquivalence A P).isQCatEquivalence.isWeakHomotopyEquivalence
  constructor
  · intro hf
    exact (strictBETotJointSourceNativeOppositeFiberMap_weak_iff_original A P).mp
      (he.cancel_right hf)
  · intro hf
    exact ((strictBETotJointSourceNativeOppositeFiberMap_weak_iff_original A P).mpr hf).comp he
end SerrePositivity.EInfinity.BarrattEccles
