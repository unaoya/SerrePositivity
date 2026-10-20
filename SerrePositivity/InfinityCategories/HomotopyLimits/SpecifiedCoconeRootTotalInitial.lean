module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalStart
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalEnd

/-!
概要：根辺の四つの全族の固定終点と、元の左右の初期 Hom 族との厳密な一致。
方針：元の三角形・四面体への長辺包含と、その初期頂点の座標を保持する。
規約：同じ全パラメータの族。使われ方：三つの比較を一つの初期 Hom 空間へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "L" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫ L
local notation "V" => tetrahedronRootEdge ≫ R

/-- 円柱の時間零の元の全族は、指定した y の上に留まる。 -/
lemma specifiedCoconeRootVerticalStartFamily_fixed :
    (specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y ≫ sliceUnderProjection W) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeRootVerticalStartFamily,
    Category.assoc (specifiedCoconeRootVerticalFamily hp p c hc dB dC y) _
      (sliceUnderProjection W),
    normalizedCoconeRestriction_projection, specifiedCoconeRootVerticalFamily_fixed]

/-- 円柱の時間一の全族も、同じ指定 y の上に留まる。 -/
lemma specifiedCoconeRootVerticalEndFamily_fixed :
    (specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫ sliceUnderProjection V) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeRootVerticalEndFamily_projection, specifiedCoconeLeftRootedHomFamily_fixed]

/-- 元の左長辺の全族の終点は、同じ y の上に留まる。 -/
lemma specifiedCoconeLeftRootTotalFamily_fixed :
    (specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y ≫ sliceUnderProjection W) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeLeftRootTotalFamily,
    Category.assoc (specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y) _
      (sliceUnderProjection W), sliceUnderRestrict_projection,
    specifiedCoconeLeftRootedHomFamily_fixed]

/-- 元の右長辺の全族も、同じ y の上に留まる。 -/
lemma specifiedCoconeRightRootTotalFamily_fixed :
    (specifiedCoconeRightRootTotalFamily hp p c hc dB dC y ≫ sliceUnderProjection V) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeRightRootTotalFamily,
    Category.assoc (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y) _
      (sliceUnderProjection V), sliceUnderRestrict_projection,
    specifiedCoconeRootedHomTetrahedronFamily_fixed]

/-- 元の左長辺の初期 Hom 族は、元の左三角形の同じ初期 Hom 族そのもの。 -/
lemma specifiedCoconeLeftRootTotalFamily_initial :
    initialDiagramHomFamily q c W (stdSimplex.δ (1 : Fin 2))
        (specifiedCoconeRootClosingLeft_initial hp p c hc dB dC) y
        (specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y)
        (specifiedCoconeLeftRootTotalFamily_fixed hp p c hc dB dC y) =
      specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y :=
  initialDiagramHomFamily_restrict q c L (stdSimplex.δ (1 : Fin 3))
    (stdSimplex.δ (1 : Fin 2)) (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
    triangleLongEdge_sourceVertex (specifiedCoconeRootClosingLeft_initial hp p c hc dB dC)
    (specifiedCoconeLeftRootedTriangle_initial hp p c hc dB dC) y
    (specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y)
    (specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)

/-- 元の右長辺の初期 Hom 族も、元の四面体からの同じ初期 Hom 族そのもの。 -/
lemma specifiedCoconeRightRootTotalFamily_initial :
    initialDiagramHomFamily q c V (stdSimplex.δ (1 : Fin 2))
        (specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC) y
        (specifiedCoconeRightRootTotalFamily hp p c hc dB dC y)
        (specifiedCoconeRightRootTotalFamily_fixed hp p c hc dB dC y) =
      specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y :=
  initialDiagramHomFamily_restrict q c R tetrahedronRootEdge
    (stdSimplex.δ (1 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)))
    tetrahedronRootEdge_source
    (specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC)
    (specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC) y
    (specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y)
    (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
