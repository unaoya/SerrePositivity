module
public import SerrePositivity.InfinityCategories.F1.Transport.CoslicePointFamilyAt
public import SerrePositivity.KST.Fibration.ScaffoldPointedReconstruction
public import SerrePositivity.InfinityCategories.F1.Transport.PointedCosliceReconstruction
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-! # 同じ scaffold 復元の恒等点からの coslice 延長は、元の全復元射と同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}} [Quasicategory B] (b : B _⦋0⦌)

/-- 元の coslice 恒等点の、指定 scaffold 三角形を保持した復元による実像。 -/
def scaffoldCosliceReconstructionPoint :=
  (leftFibrationCoslicePointEvaluate
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm b)))) b).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex _ _ (scaffoldPointedReconstruction
      (sliceUnderProjection (yonedaEquiv.symm b))) (scaffoldPointedReconstruction_projection _))

/-- 同じ点は元の恒等 coslice 辺の実 fiber 写像による像そのもの。 -/
theorem scaffoldCosliceReconstructionPoint_fiberMap :
    scaffoldCosliceReconstructionPoint b =
      (vertexFiberMap (sliceUnderProjection (yonedaEquiv.symm b))
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
          (sliceUnderProjection (yonedaEquiv.symm b))))
        (scaffoldPointedReconstruction (sliceUnderProjection (yonedaEquiv.symm b)))
        (scaffoldPointedReconstruction_projection _) b).app (Opposite.op ⦋0⦌)
          (edgeToCosliceFiberVertex (SSet.Edge.id b)) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.coslicePointEvaluation_fiberMap_identity _ b _ _

/-- 既存の点族を同じ復元恒等点で評価した、元の coslice 全体の延長。 -/
def scaffoldCoslicePointExtension :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.coslicePointFamilyAt
    (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram
      (sliceUnderProjection (yonedaEquiv.symm b)))) b (scaffoldCosliceReconstructionPoint b)

/-- 同じ恒等点から延長した全写像は、元の指定 scaffold 復元射と自然同型。 -/
def scaffoldCoslicePointExtension_reconstructionIso :
    FunctorIso (scaffoldCoslicePointExtension b)
      (scaffoldPointedReconstruction (sliceUnderProjection (yonedaEquiv.symm b))) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.coslicePointFamilyAt_recoveryIso _ b
    (scaffoldPointedReconstruction (sliceUnderProjection (yonedaEquiv.symm b)))
    (scaffoldPointedReconstruction_projection _)

/-- 同じ実恒等点からの延長は、全関手空間で前合成同値。 -/
theorem scaffoldCoslicePointExtension_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (scaffoldCoslicePointExtension b) := by
  apply (isPrecompositionEquivalence_iff_isQCatEquivalence _).mpr
  exact (scaffoldPointedReconstruction_isPrecompositionEquivalence
    (sliceUnderProjection (yonedaEquiv.symm b))).isQCatEquivalence.ofFunctorIso
      (scaffoldCoslicePointExtension_reconstructionIso b).symm

end SerrePositivity.KST.Fibration
