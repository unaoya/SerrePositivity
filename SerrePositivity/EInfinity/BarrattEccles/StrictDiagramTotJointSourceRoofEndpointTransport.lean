module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativePinched
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointTargetReplacement
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotProbeNativeHomComparison

/-!
概要：同じroof比較のprobeと右置換の両端を、元のnative Homの両端へ合わせる。
方針：元のprobe比較と元の全標的置換単位の同じ頂点同型を使う。
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
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
local instance jointRoofEndpointTransportModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofEndpointTransportFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 始域の同じprobe比較を、元のモデル源の頂点表示へ等式で移す。 -/
def strictBETotJointRoofProbeEndpointIso (P : strictBETotJointHomIndex A) :
    VertexIso
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofSourceObject A P)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop))) :=
  eqToIso (congrArg (fun v => HomotopyCategory.mk v)
    (strictBETotModelSource_vertex A (framedLimitProbe A (AsSmall.down.obj P).1.unop))) ≪≫
      strictBETotProbeSourceIso A (AsSmall.down.obj P).1.unop ≪≫
        (eqToIso (congrArg (fun v => HomotopyCategory.mk v)
          (strictBETotModelSource_vertex A (AsSmall.down.obj P).1.unop))).symm

/-- 元の全標的置換の同じ頂点は、元の右置換の対象そのもの。 -/
theorem strictBETotJointRoofTargetReplacement_vertex (P : strictBETotJointHomIndex A) :
    ((nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A).app
      (Opposite.op ⦋0⦌)) (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)) =
      (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofTargetObject A P)) := by
  have hn : (nerveMap (strictBETotTargetReplacement A)).app (Opposite.op ⦋0⦌)
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)) =
        nerveVertex (strictBETotJointRoofTargetObject A P) := by
    have hv : nerveVertex ((strictBETotJointHomTargetIndex A).obj P) =
        ComposableArrows.mk₀ ((strictBETotJointHomTargetIndex A).obj P) :=
      ComposableArrows.ext₀ rfl
    rw [hv, nerveMap_app_mk₀]
    exact ComposableArrows.ext₀ rfl
  exact congrArg ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)) hn

/-- 標的の同じ全置換単位の成分を、元の右置換の頂点へ合わせる。 -/
def strictBETotJointRoofTargetEndpointUnitIso (P : strictBETotJointHomIndex A) :
    VertexIso
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))
      ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointRoofTargetObject A P))) :=
  (strictBETotTargetReplacementNativeIso A).toNatIso.app
    (HomotopyCategory.mk (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))) ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v)
        (strictBETotJointRoofTargetReplacement_vertex A P))

/-- 同じ元のprobeと標的置換の同型で、同じ基準roofを元の両端へ輸送する。 -/
def strictBETotJointSourceRoofNormalizedPinchedComparison (P : strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
        ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))) :=
  strictBETotJointSourceRoofNativePinchedComparison A P ≫
    (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
      (strictBETotJointRoofProbeEndpointIso A P)
      (strictBETotJointRoofTargetEndpointUnitIso A P).symm).hom

/-- 元の同じ両端へ戻した基準roofの実射も弱同値。 -/
theorem strictBETotJointSourceRoofNormalizedPinchedComparison_weak
    (P : strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (strictBETotJointSourceRoofNormalizedPinchedComparison A P) :=
  (strictBETotJointSourceRoofNativePinchedComparison_weak A P).comp
    ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
      (strictBETotJointRoofProbeEndpointIso A P)
      (strictBETotJointRoofTargetEndpointUnitIso A P).symm).isQCatEquivalence.isWeakHomotopyEquivalence)
end SerrePositivity.EInfinity.BarrattEccles
