module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanTriangles
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentTransportIso

/-!
概要：span の普遍余錐の元の二単体から、輸送した二つの部分余錐の境界を結ぶ指定経路を作る。
方針：制限の輸送自然性、実際の付加比較辺、左右の三角形の輸送比較を合成する。
規約：任意の π₀ の一致から経路を選ばない。使われ方：指定経路を保つ貼り合わせへの入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ SpaceInfinity.{u}}
  (c : JoinCocone p) (hc : IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : JoinCocone G)

/-- 元の二単体と付加比較辺により指定された、右境界から左境界への点図式の同型。 -/
def partialColimitSpanBoundaryIso :
    FunctorIso
      (SSet.yonedaEquiv.symm (transportedCoconeVertex dC
          (partialColimitSpanRightLeg c hc i F hi dB j G hj dC)) ≫
        normalizedCoconeRestrictionFiber G j hj
          (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex)
      (SSet.yonedaEquiv.symm (transportedCoconeVertex dB
          (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)) ≫
        normalizedCoconeRestrictionFiber F i hi
          (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex) := by
  let eB := partialColimitSpanLeftLeg c hc i F hi dB j G hj dC
  let eC := partialColimitSpanRightLeg c hc i F hi dB j G hj dC
  let q := sliceUnderProjection p
  let v := initialFiberVertexAt q c c.vertex rfl
  have AB : FunctorIso
      (SSet.yonedaEquiv.symm (colimitAttachmentFiberVertex i F hi dB) ≫ edgeTransport q eB)
      (SSet.yonedaEquiv.symm v ≫
        (edgeTransport q (colimitAttachmentApexEdge c hc i F hi dB) ≫ edgeTransport q eB)) := by
    simpa only [Category.assoc] using FunctorIso.postcomp
      (colimitAttachmentTransportPointIso c hc i F hi dB) (edgeTransport q eB)
  have AC : FunctorIso
      (SSet.yonedaEquiv.symm (colimitAttachmentFiberVertex j G hj dC) ≫ edgeTransport q eC)
      (SSet.yonedaEquiv.symm v ≫
        (edgeTransport q (colimitAttachmentApexEdge c hc j G hj dC) ≫ edgeTransport q eC)) := by
    simpa only [Category.assoc] using FunctorIso.postcomp
      (colimitAttachmentTransportPointIso c hc j G hj dC) (edgeTransport q eC)
  let M := FunctorIso.precomp
    (partialColimitSpanTransportIso c hc i F hi dB j G hj dC q) (SSet.yonedaEquiv.symm v)
  exact ((coconeBoundaryTransportPointIso i F hi dB eB) ≪≫ AB ≪≫ M ≪≫ AC.symm ≪≫
    (coconeBoundaryTransportPointIso j G hj dC eC).symm).symm

/-- span の普遍余錐が指定する、実際の右境界から左境界への可逆経路。 -/
def partialColimitSpanBoundaryPath :
    (Δ[0] : SSet.{u + 1}) ⟶ equivalencePath
      (coconeMappingSpace p (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex) :=
  homotopyEquivalencePath
    (partialColimitSpanBoundaryIso c hc i F hi dB j G hj dC).simplicialHomotopy

/-- 指定した経路の始点は、右部分余錐を実際の右脚で輸送した余錐の境界。 -/
lemma partialColimitSpanBoundaryPath_zero :
    partialColimitSpanBoundaryPath c hc i F hi dB j G hj dC ≫ equivalencePathEndpoint _ 0 =
      SSet.yonedaEquiv.symm (transportedCoconeVertex dC
          (partialColimitSpanRightLeg c hc i F hi dB j G hj dC)) ≫
        normalizedCoconeRestrictionFiber G j hj
          (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  homotopyEquivalencePath_zero _

/-- 指定した経路の終点は、左部分余錐を実際の左脚で輸送した余錐の境界。 -/
lemma partialColimitSpanBoundaryPath_one :
    partialColimitSpanBoundaryPath c hc i F hi dB j G hj dC ≫ equivalencePathEndpoint _ 1 =
      SSet.yonedaEquiv.symm (transportedCoconeVertex dB
          (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)) ≫
        normalizedCoconeRestrictionFiber F i hi
          (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC).vertex :=
  homotopyEquivalencePath_one _

end
end SerrePositivity.InfinityCategories.HomotopyLimits
