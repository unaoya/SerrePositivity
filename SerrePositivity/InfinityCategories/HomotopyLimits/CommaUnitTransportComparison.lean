module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitTransportEndpoint
public import SerrePositivity.InfinityCategories.F1.Transport.InitialParametrizedPointTransport
public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransport

/-!
概要：標準単位比較を、同じ comma 頂点からの普遍輸送と関手同型で照合する。
方針：元の合成円柱の始点・終点・底を指定し、left fibration の輸送の一意性を使う。
規約：単位の普遍性を仮定しない。使われ方：始対象条件から写像空間の単位比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 元の合成円柱の終点は、同じ指定単位頂点で評価した普遍輸送と関手同型。 -/
def unitCommaCompositionEndpoint_transportIso (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    FunctorIso (unitCommaCompositionEndpoint η x y)
      (parametrizedFiberTransport (F1B.kanUnitCommaFiberProjection G x)
        (F.app (Opposite.op ⦋0⦌) x) y ≫
          evaluateFunctorAt (unitCommaSectionTargetFiberVertex η x)) := by
  let p := F1B.kanUnitCommaFiberProjection G x
  let v := unitCommaSectionTargetFiberVertex η x
  let P := intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry (𝟙 P))
      (intervalFamily_zero (𝟙 P)) (intervalFamily_one (𝟙 P)) = 𝟙 P := by
    apply intervalMappingUncurry_injective
    exact intervalMappingUncurry_curryOfEndpoints _ _ _
  have e := leftFibrationPrism_diagonalTransportIso p
    (SSet.const v : P ⟶ _) (unitCommaCompositionEndpoint η x y)
    (intervalMappingUncurry (𝟙 P)) (intervalFamily_zero (𝟙 P))
    (intervalFamily_one (𝟙 P)) (unitCommaCompositionPrism η x y)
    (unitCommaCompositionPrism_zero η x y)
    (unitCommaCompositionEndpoint_ι η x y).symm
    (unitCommaCompositionPrism_projection η x y)
  rw [hc] at e
  have hd : diagonalFiberTransport p (SSet.const v : P ⟶ _) (𝟙 P) =
      parametrizedFiberTransport p (F.app (Opposite.op ⦋0⦌) x) y ≫
        evaluateFunctorAt v := by
    change lift (SSet.const v) (𝟙 P) ≫
        (parametrizedFiberTransportFamily p (F.app (Opposite.op ⦋0⦌) x) y).endpoint =
      curry (parametrizedFiberTransportFamily p (F.app (Opposite.op ⦋0⦌) x) y).endpoint ≫
        evaluateFunctorAt v
    rw [curry_evaluateFunctorAt_vertex]
  rw [hd] at e
  exact e

/-- 指定単位比較そのものは、同じ単位頂点からの普遍輸送を区間模型へ移した射。 -/
def unitIntervalMap_commaTransportIso (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    FunctorIso (unitIntervalMap η x y)
      (parametrizedFiberTransport (F1B.kanUnitCommaFiberProjection G x)
        (F.app (Opposite.op ⦋0⦌) x) y ≫
          evaluateFunctorAt (unitCommaSectionTargetFiberVertex η x) ≫
            F1B.kanUnitCommaFiberToInterval G x y) := by
  simpa only [unitCommaCompositionEndpoint_interval, Category.assoc] using
    (unitCommaCompositionEndpoint_transportIso η x y).postcomp
      (F1B.kanUnitCommaFiberToInterval G x y)

end SerrePositivity.InfinityCategories.HomotopyLimits
