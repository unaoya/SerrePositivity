module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitTransportPrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaUnitRepresentative

/-!
概要：単位の合成円柱の終点を、元の標的 fiber の区間模型で計算する。
方針：標的辺の終点で fiber に制限し、普遍正方形の右辺を厳密に回収する。
規約：終点の像は指定単位比較そのもの。使われ方：普遍輸送との照合。
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

/-- 単位円柱の終点を、元の y 上の標的 fiber の族として取る。 -/
def unitCommaCompositionEndpoint (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ⟶
      vertexFiber (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y :=
  vertexFiberLift _ _ (prismEndpoint 1 _ ≫ unitCommaCompositionPrism η x y) (by
    rw [Category.assoc, unitCommaCompositionPrism_projection, intervalFamily_one])

/-- 終点の包含は、元の円柱の一端への制限そのもの。 -/
lemma unitCommaCompositionEndpoint_ι (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    unitCommaCompositionEndpoint η x y ≫
      vertexFiberι (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y =
        prismEndpoint 1 _ ≫ unitCommaCompositionPrism η x y :=
  vertexFiberLift_ι _ _ _ _

/-- 単位円柱の終点の矢印ホモトピーは、元の指定単位比較の普遍族。 -/
lemma unitCommaCompositionEndpoint_homotopy (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (unitCommaFiberHomotopy (unitCommaCompositionEndpoint η x y ≫
      vertexFiberι (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) y)).h =
        (intervalFamilyHomotopy (unitIntervalMap η x y)).h := by
  rw [unitCommaCompositionEndpoint_ι, unitCommaFiberHomotopy_precomp]
  dsimp only [unitCommaCompositionPrism]
  rw [unitCommaFiberCurry_homotopy]
  exact functorSquareCoherence_right
    (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangle η x y))

/-- 終点を元の区間模型へ写すと、標準単位比較に厳密に一致する。 -/
lemma unitCommaCompositionEndpoint_interval (η : FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    unitCommaCompositionEndpoint η x y ≫ SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval G x y =
      unitIntervalMap η x y := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_precomp, SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval_uncurry,
    ← unitCommaUncurry_precomp]
  apply (cancel_epi (β_ _ (Δ[1] : SSet.{u})).hom).mp
  exact unitCommaCompositionEndpoint_homotopy η x y

end SerrePositivity.InfinityCategories.HomotopyLimits
