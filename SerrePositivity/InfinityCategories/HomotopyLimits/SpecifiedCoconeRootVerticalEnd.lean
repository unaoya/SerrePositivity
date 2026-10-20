module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedTerminalHomotopyEnd
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootEdgeFamily

/-!
概要：同じ根辺円柱の時間一の端面と、元の右四面体の長辺族を明示する。
方針：各族を同じ実際の右長辺上に置き、底を既存の左右の根辺族へ照合する。
規約：両族の一致はまだ主張しない。使われ方：終端固定の底の比較の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
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
local notation "R" => specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "V" => tetrahedronRootEdge ≫ R
local notation "H" => specifiedCoconeRootVerticalHomotopy hp p c hc dB dC
local notation "z" => Subtype.val (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)
local notation "hz" => specifiedCoconeRootVerticalHomotopy_terminal hp p c hc dB dC
local notation "hq" => specifiedCoconeRootVerticalFamily_base_diagram hp p c hc dB dC
local notation "a" => specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_projection hp p c hc dB dC

/-- 元の同じ根辺円柱の全族の、時間一の実際の右長辺上の端面。 -/
def specifiedCoconeRootVerticalEndFamily : T ⟶ sliceUnder V :=
  specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
    normalizedCoconeRestriction (H).h SSet.ι₁ (H).h₁

/-- 時間一の端面の底は、元の左根辺の全 Hom 族そのもの。 -/
lemma specifiedCoconeRootVerticalEndFamily_base :
    (specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫ sliceUnderPostcomp V q) ≫
        eqToHom (congrArg sliceUnder hV) =
      specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y := by
  apply sliceUnderUncurry_injective (specifiedCoconeNativeRootEdge hp p c hc dB dC)
  rw [sliceUnderUncurry_eqToHom hV]
  change sliceUnderUncurry
    (fixedTerminalHomotopyEndFamily H z hz q hq a ≫ sliceUnderPostcomp V q) = _
  rw [fixedTerminalHomotopyEndFamily_base,
    sliceUnderUncurry_eqToHom (fixedTerminalHomotopy_end_base_diagram H q hq)]
  have h := congrArg sliceUnderUncurry
    (specifiedCoconeLeftRootTotalFamily_base hp p c hc dB dC y)
  simp only [← Category.assoc] at h
  rw [sliceUnderUncurry_eqToHom
    (specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC)] at h
  exact h

/-- 時間一でも元の全族の同じ終端係数を保持する。 -/
lemma specifiedCoconeRootVerticalEndFamily_terminal :
    specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫
        sliceUnderRestrict V (stdSimplex.δ (0 : Fin 2)) =
      a ≫ normalizedCoconeRestriction
        (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeLeftRootedTriangle hp p c hc dB dC)
        (stdSimplex.δ (0 : Fin 2)) (fixedTerminalHomotopy_end_terminal_diagram H z hz) :=
  fixedTerminalHomotopyEndFamily_terminal H z hz q hq a

/-- 時間一の端面も元の左三角形の可変終点の全族を保持する。 -/
lemma specifiedCoconeRootVerticalEndFamily_projection :
    specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫ sliceUnderProjection V =
      specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
        sliceUnderProjection (specifiedCoconeLeftRootedTriangle hp p c hc dB dC) := by
  change fixedTerminalHomotopyEndFamily H z hz q hq a ≫ _ = _
  rw [fixedTerminalHomotopyEndFamily_projection, specifiedCoconeLeftRootTotalFamily,
    Category.assoc, sliceUnderRestrict_projection]

/-- 比較先となる元の右四面体の、同じ実際の長辺上の全 Hom 族。 -/
def specifiedCoconeRightRootTotalFamily : T ⟶ sliceUnder V :=
  specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y ≫
    sliceUnderRestrict R tetrahedronRootEdge

/-- 元の右族の底は、既存の右根辺の全族の同じ正規化表示。 -/
lemma specifiedCoconeRightRootTotalFamily_base :
    (specifiedCoconeRightRootTotalFamily hp p c hc dB dC y ≫ sliceUnderPostcomp V q) ≫
        eqToHom (congrArg sliceUnder hV) =
      specifiedCoconeRootBaseEdgeFamily hp p c hc dB dC y := by
  apply sliceUnderUncurry_injective (specifiedCoconeNativeRootEdge hp p c hc dB dC)
  simp only [specifiedCoconeRightRootTotalFamily, specifiedCoconeRootBaseEdgeFamily]
  rw [sliceUnderUncurry_eqToHom hV, sliceUnderUncurry_postcomp,
    sliceUnderUncurry_restrict, normalizedCoconeRestriction_uncurry,
    sliceUnderUncurry_postcomp, Category.assoc]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
