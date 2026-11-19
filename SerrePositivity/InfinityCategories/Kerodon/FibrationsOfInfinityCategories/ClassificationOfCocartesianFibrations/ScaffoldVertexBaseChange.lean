module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldVertexBaseChange
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldVertexBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ScaffoldReconstructionFiberPoint

/-! # 任意の元の fiber 点に対する、元の底変換成分と scaffold 復元の自然性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  [Quasicategory B] (k : D ⟶ B) [Quasicategory D]

omit [Quasicategory B] [Quasicategory D] in
/-- 零単体の第一射影切断の初頂点は、元の指定点の実 fiber 底変換像。 -/
theorem baseChangeZeroSectionFiberPoint_eq (d : D _⦋0⦌)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p k) d) _⦋0⦌) :
    Eq.mp (congrArg (fun b => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
      (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)))
      (firstVertexSectionFiberPoint p ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor k).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d))
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.straighteningBaseChangeImageSectionPoint p k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorBaseChangeForward p k (SSet.yonedaEquiv.symm d)).app
            (Opposite.op ⦋0⦌) (vertexFiberZeroSection (pullback.snd p k) d w)))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p k d).hom.app (Opposite.op ⦋0⦌) w := by
  apply Subtype.ext
  have hv := baseChangeImageSectionFiberPoint_val p k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d)
    (vertexFiberZeroSection (pullback.snd p k) d w)
  have hz := congrArg ((pullback.fst p k).app (Opposite.op ⦋0⦌))
    (vertexFiberZeroSection_firstVertex_val (pullback.snd p k) d w)
  exact (vertexFiberPoint_eq_mp_val p
    (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)) _).trans (hv.trans hz)

/-- 元の大域底変換の同じ成分を、元の指定底頂点で表示する。 -/
def scaffoldVertexBaseChangeIso (d : D _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints (scaffoldBaseChangeCoefficientIso p k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d))
    (congrArg (fun b => HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b)))
      (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)))
    (congrArg (fun b => HomotopyCategory.mk
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (pullback.snd p k)).app
        (Opposite.op ⦋0⦌) (ULift.up b))) (zeroSimplexFirstVertex d))

omit [Quasicategory B] [Quasicategory D] in
/-- 零単体を通した表示も、元の実図式の同じ指定頂点成分そのもの。 -/
theorem scaffoldVertexBaseChangeIso_eq_diagramValue (d : D _⦋0⦌) :
    scaffoldVertexBaseChangeIso p k d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k) (ULift.up d) := by
  have hn : HEq (scaffoldVertexBaseChangeIso p k d)
      (scaffoldBaseChangeCoefficientIso p k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d)) := by
    unfold scaffoldVertexBaseChangeIso _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.isoNormalizeEndpoints
    exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.iso_endpoints_heq _ _ _
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.vertexIso_map_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k)
    (congrArg (fun z : D _⦋0⦌ => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj D) (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (ULift.up z))
      (zeroSimplexFirstVertex d))
  exact eq_of_heq (hn.trans
    ((scaffoldBaseChangeCoefficientIso_heq_diagramValue p k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d)).trans
      (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue_heq_map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k) (ULift.up d)).symm)))

/-- 元の fiber 点の第一射影による復元像は、元の底変換比較で同じ pullback 復元像へ送られる。 -/
theorem scaffoldVertexBaseChangeIso_pointHom (d : D _⦋0⦌)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p k) d) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p (k.app (Opposite.op ⦋0⦌) d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p k d).hom.app (Opposite.op ⦋0⦌) w)) ≫
        (scaffoldVertexBaseChangeIso p k d).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint (pullback.snd p k) d w) := by
  let v := vertexFiberZeroSection (pullback.snd p k) d w
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex d
  have hs := scaffoldReconstructionFiberPoint_eq_transport p
    (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)) _ _
    (baseChangeZeroSectionFiberPoint_eq p k d w)
  have ht := scaffoldReconstructionFiberPoint_eq_transport (pullback.snd p k)
    (zeroSimplexFirstVertex d) _ w (vertexFiberZeroSection_firstVertex (pullback.snd p k) d w)
  have he := scaffoldBaseChangeCoefficientIso_pointHom p k c v
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.pointNormalize _ _ _ _ _ _ _ hs ht he

/-- 任意の元の fiber 点について、復元の実像は元の図式の底変換成分と両立する。 -/
theorem scaffoldPointedReconstruction_baseChange_pointHom (d : D _⦋0⦌)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p k) d) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p (k.app (Opposite.op ⦋0⦌) d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p k d).hom.app (Opposite.op ⦋0⦌) w)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k) (ULift.up d)).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint (pullback.snd p k) d w) := by
  rw [← scaffoldVertexBaseChangeIso_eq_diagramValue p k d]
  exact scaffoldVertexBaseChangeIso_pointHom p k d w

end SerrePositivity.KST.Fibration
