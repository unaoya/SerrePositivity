module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CommaLocalUnitTransportPrism

/-!
概要：局所輸送円柱の終点で元の区間比較を回収する。
方針：円柱を終点の fiber に制限し、右辺の普遍族を計算する。
規約：始点は元の点であり、底は Y の普遍区間族そのもの。
使われ方：局所比較と普遍輸送の関手同型の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X Y : SSet.{u}} [Quasicategory X]
variable {G : Y ⟶ X} {x : X _⦋0⦌} {y₀ : Y _⦋0⦌}

/-- 概要：局所円柱の終点を標的 fiber の族として取る。
方針：終点への制限を fiber に持ち上げる。
規約：元の y 上の fiber を使用。
使われ方：局所区間比較の回収。 -/
def unitCommaCompositionEndpointAt
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    intervalMappingSpace y₀ y ⟶
      vertexFiber (F1B.unitCommaFiberProjection G x) y :=
  vertexFiberLift _ _ (prismEndpoint 1 _ ≫ unitCommaCompositionPrismAt v y) (by
    rw [Category.assoc, unitCommaCompositionPrismAt_projection, intervalFamily_one])

/-- 概要：終点族の包含を計算する。
方針：fiber の持ち上げの公式を使う。
規約：円柱の一端への制限と厳密に一致。
使われ方：輸送比較の終端条件。 -/
lemma unitCommaCompositionEndpointAt_ι
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    unitCommaCompositionEndpointAt v y ≫
      vertexFiberι (F1B.unitCommaFiberProjection G x) y =
        prismEndpoint 1 _ ≫ unitCommaCompositionPrismAt v y :=
  vertexFiberLift_ι _ _ _ _

/-- 概要：局所円柱の終点の矢印を計算する。
方針：合成正方形の右辺を回収する。
規約：元の局所比較の普遍族を保持。
使われ方：区間模型での厳密な一致。 -/
lemma unitCommaCompositionEndpointAt_homotopy
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    (unitCommaFiberHomotopy (unitCommaCompositionEndpointAt v y ≫
      vertexFiberι (F1B.unitCommaFiberProjection G x) y)).h =
        (intervalFamilyHomotopy (unitIntervalMapAt v y)).h := by
  rw [unitCommaCompositionEndpointAt_ι, unitCommaFiberHomotopy_precomp]
  dsimp only [unitCommaCompositionPrismAt]
  rw [unitCommaFiberCurry_homotopy]
  exact functorSquareCoherence_right
    (functorSquareOfCompositionTriangle (unitIntervalCompositionTriangleAt v y))

/-- 概要：終点を区間模型に写すと局所比較に一致する。
方針：展開の単射性と矢印の計算を使う。
規約：元の選択済み比較との厳密な等式。
使われ方：輸送同型の後合成。 -/
lemma unitCommaCompositionEndpointAt_interval
    (v : (vertexFiber (F1B.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    unitCommaCompositionEndpointAt v y ≫ F1B.unitCommaFiberToInterval G x y =
      unitIntervalMapAt v y := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_precomp, F1B.unitCommaFiberToInterval_uncurry,
    ← unitCommaUncurry_precomp]
  apply (cancel_epi (β_ _ (Δ[1] : SSet.{u})).hom).mp
  exact unitCommaCompositionEndpointAt_homotopy v y

end SerrePositivity.InfinityCategories.HomotopyLimits
