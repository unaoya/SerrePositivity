module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteProductIndexTransport

/-!
概要：一般有限添字へ再添字した元の native 有限積錐の各脚と全余錐比較。
方針：元の脚の全一単体の一致から Kan 射の厳密な一致を回収し、元の全余錐比較を使う。
規約：元の頂点・脚・coherent 射影・指定単位を保持する。
使われ方：P_Σ の sifted 閉性の一般有限離散図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}} [IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  {J : Type u} (e : J ≃ ULift.{u} (Fin (n + 1))) (j : Discrete J)

/-- 元の再添字錐の native な脚を、同じ元の余極限 Kan 対象の射に戻す。 -/
def reindexedFiniteProductNativeKanLeg :
    F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F) ⟶
      (reindexedFiniteProductDiagram n F e).obj j :=
  F2.kanNativeConeLeg (reindexedFiniteProductNativeCone n F e) _
    (reindexedFiniteProductNativeCone_vertex n F e) j

/-- 戻した再添字脚は、指定された元の脚そのもの。 -/
lemma reindexedFiniteProductNativeKanLeg_eq :
    reindexedFiniteProductNativeKanLeg n F e j =
      finiteSiftedCoherentProductNativeKanLeg n F (Discrete.mk (e j.as)) := by
  have h : F2.kanNativeConeLegEdge (reindexedFiniteProductNativeCone n F e) _
      (reindexedFiniteProductNativeCone_vertex n F e) j =
    F2.kanNativeConeLegEdge (finiteSiftedCoherentProductNativeCone n F) _
      (finiteSiftedCoherentProductNativeCone_vertex n F) (Discrete.mk (e j.as)) := by
    apply SSet.Edge.ext
    exact reindexedFiniteProductNativeCone_leg_edge n F e j
  exact congrArg coherentNerveEdgeToHom h

/-- 再添字した元の native 脚の Kan 像は、元の全空間射影の Kan 像にホモトピック。 -/
lemma reindexedFiniteProductNativeKanLeg_projection :
    Nonempty (SSet.Homotopy (reindexedFiniteProductNativeKanLeg n F e j)
      (F2.continuousKanReplacement.map
        (finiteCoherentSpaceProductTotalProjection n F (e j.as).down))) := by
  rw [reindexedFiniteProductNativeKanLeg_eq]
  exact finiteSiftedCoherentProductNativeKanLeg_projection n F (Discrete.mk (e j.as))

/-- 元の再添字 native 脚の全余錐作用も、元の反復射影と指定単位の合成余錐に同型。 -/
def reindexedFiniteProductNativeCoconeIso
    (T : F2.CoherentTransformationUnitTriangle (finiteCoherentSpaceProduct n F)
      (F (e j.as).down) (finiteCoherentProjectionVertex n F (e j.as).down)) :
    VertexIso (X := coconeMappingSpace (finiteCoherentSpaceProduct n F)
      (F2.coherentDiagramTotalVertex (F (e j.as).down)))
      ((coconePointHomFamily (F2.coherentDiagramTotalCocone (finiteCoherentSpaceProduct n F))
        (F2.coherentDiagramTotalVertex (F (e j.as).down))).app (Opposite.op ⦋0⦌)
          (totalKanNativeHomPoint (finiteCoherentSpaceProduct n F) (F (e j.as).down)
            (reindexedFiniteProductNativeKanLeg n F e j)))
      (F2.coconeMappingPointAt (F2.coherentTransformationUnitCocone
        (finiteCoherentSpaceProduct n F) (F (e j.as).down)
        (finiteCoherentProjectionVertex n F (e j.as).down) T)
        (F2.coherentDiagramTotalVertex (F (e j.as).down))
        (F2.coherentTransformationUnitCocone_vertex _ _ _ T)) := by
  rw [reindexedFiniteProductNativeKanLeg_eq]
  exact finiteSiftedCoherentProductNativeCoconeIso n F (Discrete.mk (e j.as)) T

end SerrePositivity.InfinityCategories.HomotopyLimits
