module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceRoofNativePinched
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointTargetReplacement
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotProbeNativeHomComparison

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：同じroof比較のprobeと右置換の両端を、元のnative Homの両端へ合わせる。
方針：元のprobe比較と元の全標的置換単位の同じ頂点同型を使う。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
local instance jointRoofEndpointTransportModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointRoofEndpointTransportFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 始域の同じprobe比較を、元のモデル源の頂点表示へ等式で移す。 -/
def strictBETotJointRoofProbeEndpointIso (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    VertexIso
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofSourceObject A P)))
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A).obj P).unop))) :=
  eqToIso (congrArg (fun v => HomotopyCategory.mk v)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_vertex A (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A (AsSmall.down.obj P).1.unop))) ≪≫
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotProbeSourceIso A (AsSmall.down.obj P).1.unop ≪≫
        (eqToIso (congrArg (fun v => HomotopyCategory.mk v)
          (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource_vertex A (AsSmall.down.obj P).1.unop))).symm

/-- 元の全標的置換の同じ頂点は、元の右置換の対象そのもの。 -/
theorem strictBETotJointRoofTargetReplacement_vertex (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    ((nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app
      (Opposite.op ⦋0⦌)) (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P)) =
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P)) := by
  have hn : (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A)).app (Opposite.op ⦋0⦌)
      (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P)) =
        nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P) := by
    have hv : nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P) =
        ComposableArrows.mk₀ ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P) :=
      ComposableArrows.ext₀ rfl
    rw [hv, nerveMap_app_mk₀]
    exact ComposableArrows.ext₀ rfl
  exact congrArg ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)) hn

/-- 標的の同じ全置換単位の成分を、元の右置換の頂点へ合わせる。 -/
def strictBETotJointRoofTargetEndpointUnitIso (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    VertexIso
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P)))
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetObject A P))) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).toNatIso.app
    (HomotopyCategory.mk (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))) ≪≫
      eqToIso (congrArg (fun v => HomotopyCategory.mk v)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetReplacement_vertex A P))

/-- 同じ元のprobeと標的置換の同型で、同じ基準roofを元の両端へ輸送する。 -/
def strictBETotJointSourceRoofNormalizedPinchedComparison (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      Basic.pinchedHom
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A).obj P).unop)))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
          (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofNativePinchedComparison A P ≫
    (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofProbeEndpointIso A P)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetEndpointUnitIso A P).symm).hom

/-- 元の同じ両端へ戻した基準roofの実射も弱同値。 -/
theorem strictBETotJointSourceRoofNormalizedPinchedComparison_weak
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofNormalizedPinchedComparison A P) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofNativePinchedComparison_weak A P).comp
    ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofProbeEndpointIso A P)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofTargetEndpointUnitIso A P).symm).isQCatEquivalence.isWeakHomotopyEquivalence)
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
