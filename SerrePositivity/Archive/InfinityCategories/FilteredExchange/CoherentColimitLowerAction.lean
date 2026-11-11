module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerComposite
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTargetVertex

/-!
概要：元の対角の全空間作用を、元の余極限指定辺の実際の fiber 輸送へ比較する。
方針：全族の下三角形比較を一点で評価し、元の fiber 写像による前合成を回収する。
規約：元の対角・指定辺・選んだ輸送を保持。使われ方：a6 との辺比較の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の余極限の指定辺に沿う、元の始域余錐の頂点からの実際の fiber 輸送。 -/
def coherentColimitFiberTransport :
    vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex ⟶
      vertexFiber pointedSpaceProjection (coherentDiagramTotalVertex G) :=
  (functorVertexEquiv _ _).symm ((pointedIntervalTransport
    (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))).map.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 元の対角変換の全空間から元の標的の値への作用。 -/
def coherentColimitLowerAction :=
  (leftUnstraighteningMappingVertexMap F (SSet.const (coherentDiagramTotalVertex G))
    (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H))).val ≫
    constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (coherentDiagramTotalVertex G) ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom

/-- 元の対角の作用は、元の余錐の fiber 写像の後の指定余極限辺の実際の輸送に同型。 -/
def coherentColimitLowerActionIso : FunctorIso (coherentColimitLowerAction B H)
    (coconeFiberMap (coherentDiagramTotalCocone F) ≫ coherentColimitFiberTransport B H ≫
      (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom) := by
  let v := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  let m := (ihom (leftUnstraightening F)).map
    (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom
  have e := ((coherentColimitLowerFiberHomIso B H).postcomp m).app v
  have et : functorVertex (coherentColimitFiberTransport B H) =
      (pointedIntervalTransport
        (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))).map.app
          (Opposite.op ⦋0⦌) v := (functorVertexEquiv _ _).apply_symm_apply _
  have ht := congrArg (fun w => m.app (Opposite.op ⦋0⦌)
    (((pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
      (vertexFiber pointedSpaceProjection (coherentDiagramTotalVertex G))).app
        (Opposite.op ⦋0⦌) w)) et
  have es : VertexIso (X := (ihom (leftUnstraightening F)).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (coherentDiagramTotalVertex G)).obj))
      ((coherentConstantTargetMap F (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
        (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H)))
      (m.app (Opposite.op ⦋0⦌)
        (((pre (coconeFiberMap (coherentDiagramTotalCocone F))).app
          (vertexFiber pointedSpaceProjection (coherentDiagramTotalVertex G))).app
            (Opposite.op ⦋0⦌) ((pointedIntervalTransport
              (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))).map.app
                (Opposite.op ⦋0⦌) v))) := by
    change VertexIso (m.app (Opposite.op ⦋0⦌)
      ((constantUnstraighteningRelativeIso (leftUnstraighteningProjection F)
        (coherentDiagramTotalVertex G)).hom.app (Opposite.op ⦋0⦌)
          ((leftUnstraighteningMappingSpaceMap F (SSet.const (coherentDiagramTotalVertex G))).app
            (Opposite.op ⦋0⦌) (PinchedHom.constant
              (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H)) 0)))) _ at e
    rw [PinchedHom.constant_zero] at e
    exact e
  rw [coherentConstantTargetMap_vertex] at es
  exact es ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk ht.symm)

end SerrePositivity.InfinityCategories.F2
