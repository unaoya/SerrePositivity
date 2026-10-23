module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalNativeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FullyFaithfulVertexIsoImage

/-!
概要：a6 の元の区間 native 比較を、同じ普遍輸送射による指定像へ戻す。
方針：構成時の元の二成分と元の fiber 輸送比較をそのまま保持する。
規約：元の比較を再選択しない。使われ方：完成済み三角形比較の像による検証。
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
local notation "x₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "y₀" => coherentDiagramTotalVertex G

/-- 元の区間 native 比較を定める、元の二つの輸送の同じ指定像。 -/
def coherentColimitIntervalNativeImageIso : VertexIso
    ((parametrizedFiberTransport pointedSpaceProjection x₀ y₀).app (Opposite.op ⦋0⦌)
      (coherentColimitIntervalVertex B H))
    ((parametrizedFiberTransport pointedSpaceProjection x₀ y₀).app (Opposite.op ⦋0⦌)
      ((pinchedHomLeftToIntervalMappingSpace x₀ y₀).app (Opposite.op ⦋0⦌)
        (coherentTotalMapNativeRepresentation F G
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1)) := by
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
  exact h

/-- 元の区間 native 比較の普遍輸送による像は、構成時の同じ指定像そのもの。 -/
lemma coherentColimitIntervalNativeIso_image :
    VertexIso.map (coherentColimitIntervalNativeIso B H)
      (parametrizedFiberTransport pointedSpaceProjection x₀ y₀) =
      coherentColimitIntervalNativeImageIso B H := by
  unfold coherentColimitIntervalNativeIso coherentColimitIntervalNativeImageIso
  dsimp only
  exact vertexIso_map_preimage _ _

end SerrePositivity.InfinityCategories.F2
