module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootInitialComparisonIso

/-!
概要：右の初期 Hom 比較の底を、元の同じ根辺の全比較円柱へ照合する。
方針：fiber 包含後に図式の表示変更を消し、同じ頂点制限の uncurry を比較する。
規約：raw な底の円柱の厳密な等式。使われ方：指定した底の類を持つ評価固定代表。
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
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := sliceUnder (f ≫ (i ≫ p)))) c
local notation "e" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "V" => tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC
local notation "K" => specifiedCoconeRootVerticalEndComparison hp p c hc dB dC y
local notation "H" => specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y
local notation "G" => specifiedCoconeRootFamilyComparison hp p c hc dB dC y
local notation "P" => leftFibrationInitialProjection q c y
local notation "N" => normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2))
  (specifiedCoconeNativeRootEdge_source hp p c hc dB dC)

/-- 右の初期 Hom 比較の射影は、元の同じ根辺の比較円柱の初期頂点制限である。 -/
lemma specifiedCoconeRootEndInitialHomotopy_projection :
    (H).h ≫ P = (G).h ≫ normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2))
      (specifiedCoconeNativeRootEdge_source hp p c hc dB dC) y := by
  apply vertexFiber_hom_ext (sliceUnderProjection (v ≫ q)) y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, coconeVertexDiagram,
    vertexFiberMap_ι]
  rw [specifiedCoconeRootEndInitialHomotopy_base]
  rw [← Category.assoc (G).h (vertexFiberι (sliceUnderProjection e) y) N,
    ← specifiedCoconeRootVerticalEndComparison_native_base hp p c hc dB dC y]
  apply sliceUnderUncurry_injective (v ≫ q)
  rw [normalizedCoconeRestriction_uncurry, normalizedCoconeRestriction_uncurry,
    sliceUnderUncurry_eqToHom hV]

/-- 通常の Hom 空間表示でも、元の初期射影比較の raw な円柱と厳密に一致する。 -/
lemma specifiedCoconeRootEndInitialHomotopy_native_projection :
    (H).h ≫ P ≫ (leftFibrationInitialBaseIso q c y).hom =
      (specifiedCoconeRootInitialProjectionComparison hp p c hc dB dC y).h := by
  rw [← Category.assoc (H).h P (leftFibrationInitialBaseIso q c y).hom,
    specifiedCoconeRootEndInitialHomotopy_projection, Category.assoc]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
