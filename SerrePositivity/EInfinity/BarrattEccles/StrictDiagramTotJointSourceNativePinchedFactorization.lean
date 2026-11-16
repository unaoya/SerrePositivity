module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativePinched

/-! 元のnative pinched射の定義式を独立させ、同じ指定比較への係数移送に使う。 -/

@[expose] public noncomputable section
set_option autoImplicit false
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
local instance nativePinchedFactorizationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance nativePinchedFactorizationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩



attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の射の因子は同じ頂点の等式による輸送と同じ指定pinched比較。 -/
lemma strictBETotJointSourceNativePinchedMap_factorization (P : strictBETotJointHomIndex A) : strictBETotJointSourceNativePinchedMap A P =
      strictBETotJointSourceNativeOppositeFiberMap A P ≫
        (SSet.opFunctor.mapIso (eqToIso
          (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
            (strictBETotJointNativeHomInput_model_vertex A P)))).hom ≫
        (twistedArrowHomOppositePinchedEquivalence
          ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
          ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
            (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))).hom := rfl


end SerrePositivity.EInfinity.BarrattEccles
