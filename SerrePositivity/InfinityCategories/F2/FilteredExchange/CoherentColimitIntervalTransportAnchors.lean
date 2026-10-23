module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitIntervalNativeComparison

/-!
概要：元の区間 native 比較を構成する二つの指定普遍輸送成分を明示する。
方針：元の completed 輸送と元の native 輸送の頂点表示だけを揃える。
規約：元の成分を再選択しない。使われ方：完成済み比較の同じ像の指定正方形。
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
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "y" => coherentDiagramTotalVertex G
local notation "P" => parametrizedFiberTransport pointedSpaceProjection x y
local notation "q" => pinchedHomLeftToIntervalMappingSpace x y
local notation "n" => Sigma.fst (coherentTotalMapNativeRepresentation F G
  (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)))

/-- 元の completed 輸送を普遍輸送の像へ移す、元の同じ指定成分。 -/
def coherentColimitIntervalCompletedTransportIso :
    VertexIso (functorVertex (coherentColimitFiberTransport B H))
      ((parametrizedFiberTransport pointedSpaceProjection x y).app (Opposite.op ⦋0⦌)
        (coherentColimitIntervalVertex B H)) := by
  let a := SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H)
  let pt := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have ec := (pointedIntervalTransport_mapIso a).app pt
  change VertexIso ((pointedIntervalTransport a).map.app (Opposite.op ⦋0⦌) pt)
    ((parametrizedFiberTransport pointedSpaceProjection x y).app (Opposite.op ⦋0⦌)
      (PinchedHom.constant (coherentColimitIntervalVertex B H) 0)) at ec
  rw [PinchedHom.constant_zero] at ec
  have hc : functorVertex (coherentColimitFiberTransport B H) =
      (pointedIntervalTransport a).map.app (Opposite.op ⦋0⦌) pt :=
    (functorVertexEquiv _ _).apply_symm_apply _
  exact eqToIso (congrArg SSet.HomotopyCategory.mk hc) ≪≫ ec

/-- 元の native 輸送を同じ普遍輸送の像へ移す、元の同じ指定成分。 -/
def coherentColimitIntervalNativeTransportIso :
    VertexIso (functorVertex (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))))
      ((parametrizedFiberTransport pointedSpaceProjection x y).app (Opposite.op ⦋0⦌)
        ((pinchedHomLeftToIntervalMappingSpace x y).app (Opposite.op ⦋0⦌)
          (Sigma.fst (coherentTotalMapNativeRepresentation F G
            (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)))))) := by
  have en := (pointedIntervalTransport_mapIso q).app n
  have hn : functorVertex (coherentTotalMapNativeFiberTransport F G
      (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))) =
      (pointedIntervalTransport q).map.app (Opposite.op ⦋0⦌) n :=
    (functorVertexEquiv _ _).apply_symm_apply _
  exact eqToIso (congrArg SSet.HomotopyCategory.mk hn) ≪≫ en

end SerrePositivity.InfinityCategories.F2
