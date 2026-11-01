module

public import SerrePositivity.InfinityCategories.F2.Idempotent.EquivalenceRetractSquares
public import SerrePositivity.InfinityCategories.F2.Idempotent.MappingRetractionNaturality
public import SerrePositivity.InfinityCategories.Core.Retracts
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeInitialBoundaryCriterion

/-!
概要：元の相対始対象性と相対始点境界充填は、元の全圏内の retract で閉じる。
方針：前合成の全自然同型から写像空間比較の実際の retract 正方形を構成する。
規約：元の比較射そのものの同値性を戻し、単なる Hom 集合の全単射で代用しない。
使われ方：全普遍余錐の全部分 ∞ 圏の retract 閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の retract は、全区間 Hom の前合成の合成を恒等へ結ぶ全自然同型を与える。 -/
def VertexRetraction.intervalPrecompose_retractIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (z : X _⦋0⦌) :
    FunctorIso (intervalPrecompose z r.r ≫ intervalPrecompose z r.i)
      (𝟙 (intervalMappingSpace x z)) := by
  have h := intervalPrecompose_comp z r.i r.r
  rw [r.retract] at h
  exact functorIsoOfSimplicialHomotopy h.some ≪≫
    functorIsoOfSimplicialHomotopy (intervalPrecompose_id x z).some

/-- 元の相対始対象の指定 retract は、同じ元の射について相対始対象。 -/
lemma relativeInitial_of_vertexRetraction {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) {x y : X _⦋0⦌}
    (r : VertexRetraction x y) (hy : F1B.KanRelativeInitialVertex p y) :
    F1B.KanRelativeInitialVertex p x := by
  intro z
  let rp : VertexRetraction (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y) :=
    r.map (hoFunctor.map p).toFunctor
  have hg := (pinchedHomMap_equivalence_iff_intervalFunctorMap p y z).mp
    (hy z).isQCatEquivalence
  have h := isQCatEquivalence_of_retractSquares
    (intervalFunctorMap p x z) (intervalFunctorMap p y z)
    (intervalPrecompose z r.r) (intervalPrecompose z r.i)
    (intervalPrecompose (p.app (Opposite.op ⦋0⦌) z) rp.r)
    (intervalPrecompose (p.app (Opposite.op ⦋0⦌) z) rp.i)
    (VertexRetraction.intervalPrecompose_retractIso r z)
    (VertexRetraction.intervalPrecompose_retractIso rp (p.app (Opposite.op ⦋0⦌) z))
    (intervalFunctorMap_precomposeHoIso p r.r z).symm
    (intervalFunctorMap_precomposeHoIso p r.i z).symm hg
  have hp := (pinchedHomMap_equivalence_iff_intervalFunctorMap p x z).mpr h
  exact hp.isSimplicialHomotopyEquivalence

/-- 元の inner fibration の相対始点境界充填は、同じ元の頂点の retract で閉じる。 -/
lemma initialBoundaryLifting_of_vertexRetraction {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {x y : X _⦋0⦌} (r : VertexRetraction x y) (hy : InitialBoundaryLifting p y) :
    InitialBoundaryLifting p x :=
  F1B.kanInitialBoundaryLifting_of_relativeInitial p x
    (relativeInitial_of_vertexRetraction p r
      (F1B.kanRelativeInitialVertex_of_initialBoundary p y hy))

end SerrePositivity.InfinityCategories.F2.Idempotent
