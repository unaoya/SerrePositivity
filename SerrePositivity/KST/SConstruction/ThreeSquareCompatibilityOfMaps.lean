module
public import SerrePositivity.KST.SConstruction.MappingSquareCornerIdentities
public import SerrePositivity.KST.SConstruction.ThreeSquareCompatibilityData

/-! # 元の三正方形からの比較データの実構成
概要：共有二区間・定数外側二辺・指定三角形から、全境界付きデータを構成する。
方針：角の等号だけを輸送し、各 raw な辺・正方形・指定三角形は元のまま残す。
規約：端点や境界入力の存在を追加仮定にせず、与えられた実セルから導く。
使われ方：元の K 合成 prism の適合区間の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の六セルから、全境界と全セルを保持する比較入力を実構成する。 -/
def threeSquareCompatibilityDataOfMaps {E : SSet.{u}}
    (q₀ q₁ q₂ : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
    (h₁ : pastingSquareVertical 0 ≫ q₀ = pastingSquareVertical 0 ≫ q₁)
    (h₂ : pastingSquareHorizontal 0 ≫ q₁ = pastingSquareHorizontal 0 ≫ q₂)
    (vU vL : E _⦋0⦌)
    (hcU : pastingSquareVertical 1 ≫ q₀ = SSet.const vU)
    (hcL : pastingSquareHorizontal 1 ≫ q₂ = SSet.const vL)
    (t₀ t₁ t₂ : (Δ[2] : SSet.{u}) ⟶ E)
    (ht₀₂ : stdSimplex.δ 2 ≫ t₀ = pastingSquareHorizontal 0 ≫ q₀)
    (ht₀₁ : stdSimplex.δ 1 ≫ t₀ = pastingSquareVertical 0 ≫ q₂)
    (ht₁₂ : stdSimplex.δ 2 ≫ t₁ = pastingSquareHorizontal 1 ≫ q₀)
    (ht₁₁ : stdSimplex.δ 1 ≫ t₁ = pastingSquareHorizontal 1 ≫ q₁)
    (ht₂₂ : stdSimplex.δ 2 ≫ t₂ = pastingSquareVertical 1 ≫ q₁)
    (ht₂₁ : stdSimplex.δ 1 ≫ t₂ = pastingSquareVertical 1 ≫ q₂) :
    ThreeSquareCompatibilityData E := by
  let hL₀ := mappingSquareVertical_shared_corner 0 0 h₁
  let hL₁ := mappingSquareVertical_shared_corner 0 1 h₁
  let hB₀ := mappingSquareHorizontal_shared_corner 0 0 h₂
  let hB₁ := mappingSquareHorizontal_shared_corner 1 0 h₂
  let hU₀ := mappingSquareVertical_constant_corner 1 0 vU hcU
  let hU₁ := mappingSquareVertical_constant_corner 1 1 vU hcU
  let hD₀ := mappingSquareHorizontal_constant_corner 0 1 vL hcL
  let hD₁ := mappingSquareHorizontal_constant_corner 1 1 vL hcL
  let upper := mappingEdgeRetarget (mappingSquareHorizontalEdge q₀ 0) hL₀ rfl
  let lower := mappingEdgeRetarget (mappingSquareVerticalEdge q₂ 0) hB₀.symm rfl
  let left := mappingSquareVerticalEdge q₁ 0
  let bottom := mappingSquareHorizontalEdge q₁ 0
  let firstU := mappingEdgeRetarget (mappingSquareHorizontalEdge q₀ 1)
    hL₁ (hU₁.trans hU₀.symm)
  let firstL := mappingSquareHorizontalEdge q₁ 1
  let secondU := mappingSquareVerticalEdge q₁ 1
  let secondL := mappingEdgeRetarget (mappingSquareVerticalEdge q₂ 1)
    hB₁.symm (hD₁.trans hD₀.symm)
  have hu : SSet.yonedaEquiv.symm upper.edge = pastingSquareHorizontal 0 ≫ q₀ :=
    mappingSquareHorizontalEdge_map q₀ 0
  have hl : SSet.yonedaEquiv.symm lower.edge = pastingSquareVertical 0 ≫ q₂ :=
    mappingSquareVerticalEdge_map q₂ 0
  have hfu : SSet.yonedaEquiv.symm firstU.edge = pastingSquareHorizontal 1 ≫ q₀ :=
    mappingSquareHorizontalEdge_map q₀ 1
  have hfl : SSet.yonedaEquiv.symm firstL.edge = pastingSquareHorizontal 1 ≫ q₁ :=
    mappingSquareHorizontalEdge_map q₁ 1
  have hsu : SSet.yonedaEquiv.symm secondU.edge = pastingSquareVertical 1 ≫ q₁ :=
    mappingSquareVerticalEdge_map q₁ 1
  have hsl : SSet.yonedaEquiv.symm secondL.edge = pastingSquareVertical 1 ≫ q₂ :=
    mappingSquareVerticalEdge_map q₂ 1
  let hT₀₂ := mappingTriangleFaceEdge t₀ 2 upper (ht₀₂.trans hu.symm)
  let hT₀₁ := mappingTriangleFaceEdge t₀ 1 lower (ht₀₁.trans hl.symm)
  let hT₁₂ := mappingTriangleFaceEdge t₁ 2 firstU (ht₁₂.trans hfu.symm)
  let hT₁₁ := mappingTriangleFaceEdge t₁ 1 firstL (ht₁₁.trans hfl.symm)
  let hT₂₂ := mappingTriangleFaceEdge t₂ 2 secondU (ht₂₂.trans hsu.symm)
  let hT₂₁ := mappingTriangleFaceEdge t₂ 1 secondL (ht₂₁.trans hsl.symm)
  refine {
    origin := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex q₁ 0 0
    left := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex q₁ 0 1
    bottom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex q₁ 1 0
    upper := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex q₀ 1 0
    middle := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex q₁ 1 1
    lower := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex q₂ 0 1
    upperLeg := upper
    lowerLeg := lower
    leftLeg := left
    bottomLeg := bottom
    firstUpper := firstU
    firstLower := firstL
    secondUpper := secondU
    secondLower := secondL
    composite := mappingOuterTriangleEdge upper lower (SSet.yonedaEquiv t₀) hT₀₂ hT₀₁
    first := mappingOuterTriangleEdge firstU firstL (SSet.yonedaEquiv t₁) hT₁₂ hT₁₁
    second := mappingOuterTriangleEdge secondU secondL (SSet.yonedaEquiv t₂) hT₂₂ hT₂₁
    firstSquare := ⟨q₀, hu.symm, hfu.symm, ?_, ?_⟩
    middleSquare := ⟨q₁, (mappingSquareHorizontalEdge_map q₁ 0).symm, hfl.symm,
      (mappingSquareVerticalEdge_map q₁ 0).symm, hsu.symm⟩
    lastSquare := ⟨q₂, ?_, ?_, hl.symm, hsl.symm⟩
    compositeTriangle := mappingOuterTriangle upper lower (SSet.yonedaEquiv t₀) hT₀₂ hT₀₁
    firstTriangle := mappingOuterTriangle firstU firstL (SSet.yonedaEquiv t₁) hT₁₂ hT₁₁
    secondTriangle := mappingOuterTriangle secondU secondL (SSet.yonedaEquiv t₂) hT₂₂ hT₂₁ }
  · exact h₁.trans (mappingSquareVerticalEdge_map q₁ 0).symm
  · rw [mappingIdentityEdge_map]
    exact hcU.trans (congrArg SSet.const hU₀.symm)
  · exact h₂.symm.trans (mappingSquareHorizontalEdge_map q₁ 0).symm
  · rw [mappingIdentityEdge_map]
    exact hcL.trans (congrArg SSet.const hD₀.symm)

end SerrePositivity.KST.SConstruction
