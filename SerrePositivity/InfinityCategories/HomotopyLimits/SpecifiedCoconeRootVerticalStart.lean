module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedTerminalHomotopyStartComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalFamily

/-!
概要：同じ根辺円柱の時間零の端面を、元の左三角形の全 Hom 族へ相対的に接続する。
方針：底と終端の厳密な一致を用いる比較を、元の同じ具体的な円柱と族へ適用する。
規約：終端・底・可変終点を全時刻固定する。使われ方：指定余極限の全 Hom 作用の照合。
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
local notation "hq" => specifiedCoconeRootVerticalFamily_base_diagram hp p c hc dB dC
local notation "a" => specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の同じ根辺円柱上の全 Hom 族の、時間零の実際の端面。 -/
def specifiedCoconeRootVerticalStartFamily : T ⟶ sliceUnder W :=
  specifiedCoconeRootVerticalFamily hp p c hc dB dC y ≫
    normalizedCoconeRestriction (H).h SSet.ι₀ (H).h₀

/-- 元の左三角形の長辺族へ、終端と底を固定して戻す実際の円柱。 -/
def specifiedCoconeRootVerticalStartComparison :
    SSet.Homotopy (specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y) a :=
  fixedTerminalHomotopyStartComparison H z hz q hq a

/-- 比較は元の左長辺族の終端係数を全時刻で保持する。 -/
lemma specifiedCoconeRootVerticalStartComparison_terminal :
    (specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
        sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) =
      fst T Δ[1] ≫ a ≫ sliceUnderRestrict W (stdSimplex.δ (0 : Fin 2)) :=
  fixedTerminalHomotopyStartComparison_terminal H z hz q hq a

/-- 比較は元の左長辺族の底も全時刻で保持する。 -/
lemma specifiedCoconeRootVerticalStartComparison_base :
    (specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
        sliceUnderPostcomp W q = fst T Δ[1] ≫ a ≫ sliceUnderPostcomp W q :=
  fixedTerminalHomotopyStartComparison_base H z hz q hq a

/-- 可変終点は、元の左三角形の同じ全 Hom 族のまま全時刻で固定する。 -/
lemma specifiedCoconeRootVerticalStartComparison_projection :
    (specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
        sliceUnderProjection W =
      fst T Δ[1] ≫ specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y ≫
        sliceUnderProjection L := by
  simp only [specifiedCoconeRootVerticalStartComparison,
    fixedTerminalHomotopyStartComparison_projection, specifiedCoconeLeftRootTotalFamily,
    Category.assoc, sliceUnderRestrict_projection]

/-- 比較の底の終点も、元の指定 y で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalStartComparison_fixed :
    ((specifiedCoconeRootVerticalStartComparison hp p c hc dB dC y).h ≫
      sliceUnderProjection W) ≫ q = SSet.const y := by
  rw [specifiedCoconeRootVerticalStartComparison_projection]
  have h := congrArg (fun k ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ k)
    (specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)
  simpa only [Category.assoc, SSet.comp_const] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
