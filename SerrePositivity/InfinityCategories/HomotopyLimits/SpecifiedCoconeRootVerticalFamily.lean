module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedTerminalHomotopyFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootEdgeFamily

/-!
概要：元の左三角形の全 Hom 族を、同じ根辺円柱全体へ延長する。
方針：長辺へ制限してから、底と終端係数を固定した相対 coslice の充填を使う。
規約：元の左族・根辺円柱・可変終点を保持する。使われ方：左右の全 Hom 作用の比較。
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
local notation "L" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫ L
local notation "H" => specifiedCoconeRootVerticalHomotopy hp p c hc dB dC
local notation "z" => Subtype.val (specifiedCoconeRootVerticalEndpointVertex hp p c hc dB dC)
local notation "hz" => specifiedCoconeRootVerticalHomotopy_terminal hp p c hc dB dC
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 同じ元の左三角形の全 Hom 族を、その実際の長辺へ制限する。 -/
def specifiedCoconeLeftRootTotalFamily : T ⟶ sliceUnder W :=
  specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
    sliceUnderRestrict L (stdSimplex.δ (1 : Fin 3))

/-- 制限後の底は、既存の左根辺族の同じ正規化表示である。 -/
lemma specifiedCoconeLeftRootTotalFamily_base :
    specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y ≫ sliceUnderPostcomp W q ≫
        eqToHom (congrArg sliceUnder
          (specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC)) =
      specifiedCoconeLeftRootBaseEdgeFamily hp p c hc dB dC y := by
  apply sliceUnderUncurry_injective (specifiedCoconeNativeRootEdge hp p c hc dB dC)
  simp only [specifiedCoconeLeftRootTotalFamily, specifiedCoconeLeftRootBaseEdgeFamily,
    ← Category.assoc]
  rw [sliceUnderUncurry_eqToHom
      (specifiedCoconeLeftRootedTriangle_rootProjection hp p c hc dB dC),
    sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict,
    normalizedCoconeRestriction_uncurry, sliceUnderUncurry_postcomp, Category.assoc]

/-- 同じ根辺円柱の底は、元の左長辺の時間に依存しない引き戻し。 -/
lemma specifiedCoconeRootVerticalFamily_base_diagram :
    fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ (W ≫ q) = (H).h ≫ q := by
  rw [specifiedCoconeLeftRootedTriangle_rootProjection,
    specifiedCoconeRootVerticalHomotopy_projection]

local notation "hq" => specifiedCoconeRootVerticalFamily_base_diagram hp p c hc dB dC
local notation "a" => specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y

/-- 底・終端の全係数を保つ、同じ実際の根辺円柱上の全 Hom 族。 -/
def specifiedCoconeRootVerticalFamily : T ⟶ sliceUnder (H).h :=
  fixedTerminalHomotopyFamily H z hz q hq a

/-- 終端の族は元の左族の同じ引き戻しであり、時間に依存しない。 -/
lemma specifiedCoconeRootVerticalFamily_terminal :
    specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
        sliceUnderRestrict (H).h (prismEndpoint 1 Δ[1]) =
      a ≫ normalizedCoconeRestriction W (prismEndpoint 1 Δ[1] ≫ fst Δ[1] Δ[1])
        (fixedTerminalHomotopyFamily_terminal_diagram H z hz) :=
  fixedTerminalHomotopyFamily_terminal H z hz q hq a

/-- 底の全族も元の左長辺上の族の引き戻しそのもの。 -/
lemma specifiedCoconeRootVerticalFamily_base :
    specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫ sliceUnderPostcomp (H).h q =
      (a ≫ sliceUnderPostcomp W q) ≫
        normalizedCoconeRestriction (W ≫ q) (fst Δ[1] Δ[1]) hq :=
  fixedTerminalHomotopyFamily_base H z hz q hq a

/-- E 内の可変終点も、元の左三角形から得た同じ全族である。 -/
lemma specifiedCoconeRootVerticalFamily_projection :
    specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫ sliceUnderProjection (H).h =
      specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫ sliceUnderProjection L := by
  rw [specifiedCoconeRootVerticalFamily, fixedTerminalHomotopyFamily_projection,
    specifiedCoconeLeftRootTotalFamily, Category.assoc, sliceUnderRestrict_projection]

/-- 底の終点は全 Hom パラメータで元の指定 y のまま固定する。 -/
lemma specifiedCoconeRootVerticalFamily_fixed :
    (specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫ sliceUnderProjection (H).h) ≫ q =
      SSet.const y := by
  rw [specifiedCoconeRootVerticalFamily_projection,
    specifiedCoconeLeftRootedHomFamily_fixed]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
