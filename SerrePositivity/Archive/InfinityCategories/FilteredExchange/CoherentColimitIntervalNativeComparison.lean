module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitFiberTransportComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedIntervalTransportUniversal

/-!
概要：余極限関手の元の指定辺を、a6 の元の指定 native 辺と写像空間内で比較する。
方針：二つの輸送を同じ普遍輸送射の像へ移し、その充満忠実性で元の辺へ反映する。
規約：選択済み native 辺を保持。使われ方：元の全錐と指定 path の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の余極限指定辺は、a6 の元の指定 native 辺の同じ区間写像空間内の表示に同型。 -/
def coherentColimitIntervalNativeIso : VertexIso
    (X := intervalMappingSpace (coherentDiagramTotalCocone F).vertex
      (coherentDiagramTotalVertex G))
    (coherentColimitIntervalVertex B H)
    ((pinchedHomLeftToIntervalMappingSpace (coherentDiagramTotalCocone F).vertex
      (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
        (coherentTotalMapNativeRepresentation F G
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1) := by
  let x := (coherentDiagramTotalCocone F).vertex
  let y := coherentDiagramTotalVertex G
  let P := parametrizedFiberTransport pointedSpaceProjection x y
  let a := SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)
  let pt := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  let q := pinchedHomLeftToIntervalMappingSpace x y
  let n := (coherentTotalMapNativeRepresentation F G
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1
  have ec := (pointedIntervalTransport_mapIso a).app pt
  change VertexIso ((pointedIntervalTransport a).map.app (Opposite.op ⦋0⦌) pt)
    (P.app (Opposite.op ⦋0⦌) (PinchedHom.constant (coherentColimitIntervalVertex B H) 0)) at ec
  rw [PinchedHom.constant_zero] at ec
  have hc : functorVertex (coherentColimitFiberTransport B H) =
      (pointedIntervalTransport a).map.app (Opposite.op ⦋0⦌) pt :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have en := (pointedIntervalTransport_mapIso q).app n
  have hn : functorVertex (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) =
      (pointedIntervalTransport q).map.app (Opposite.op ⦋0⦌) n :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have h := (eqToIso (congrArg SSet.HomotopyCategory.mk hc) ≪≫ ec).symm ≪≫
    coherentColimitFiberTransportIso B H ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk hn) ≪≫ en)
  have hp := parametrizedPointedSpaceTransport_isQCatEquivalence x y
  exact hp.isFullyFaithful.preimageVertexIso h

end SerrePositivity.InfinityCategories.F2
