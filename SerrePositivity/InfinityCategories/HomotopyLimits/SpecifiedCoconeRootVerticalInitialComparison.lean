module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceRetractionSectionComparison
public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalInitialBase
public import SerrePositivity.InfinityCategories.F1.TriangleLongEdge

/-!
概要：根辺円柱の始点側の全族を、時間零・一の同じ初期 Hom 係数の間で比較する。
方針：時間に依存しない底の厳密な等式を二切断の相対比較へ入力する。
規約：底と可変終点を全時刻固定する。使われ方：左右の元の Hom 作用への接続。
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
local notation "v" => Equiv.symm (SSet.yonedaEquiv (X := sliceUnder (f ≫ (i ≫ p)))) c
local notation "r" => stdSimplex.σ (0 : Fin 1)
local notation "a" => specifiedCoconeRootVerticalInitialFamily hp p c hc dB dC y
local notation "b" => specifiedCoconeRootVerticalInitialBaseFamily hp p c hc dB dC y
local notation "hb" => specifiedCoconeRootVerticalInitialFamily_base hp p c hc dB dC y
local notation "s₀" => stdSimplex.δ (1 : Fin 2)
local notation "s₁" => stdSimplex.δ (0 : Fin 2)
local notation "h₀" => intervalRetraction_endpoint (1 : Fin 2)
local notation "h₁" => intervalRetraction_endpoint (0 : Fin 2)
local notation "P₀" => normalizedCoconeRestriction (r ≫ v) s₀
  (cosliceRetractionFamily_diagram v r s₀ h₀)
local notation "P₁" => normalizedCoconeRestriction (r ≫ v) s₁
  (cosliceRetractionFamily_diagram v r s₁ h₁)
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の根辺円柱の初期側で、二時刻の全余錐族を底を固定して結ぶ。 -/
def specifiedCoconeRootVerticalInitialComparison : SSet.Homotopy (a ≫ P₀) (a ≫ P₁) :=
  cosliceRetractionSectionComparison v r s₁ h₁ endpointInclusion_rightAnodyne q a b hb s₀ h₀

/-- 比較の底は、元の時間零の初期 Hom の係数で全時刻固定する。 -/
lemma specifiedCoconeRootVerticalInitialComparison_base :
    (specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
        sliceUnderPostcomp v q = fst T Δ[1] ≫ (a ≫ P₀) ≫ sliceUnderPostcomp v q :=
  cosliceRetractionSectionComparison_base v r s₁ h₁ endpointInclusion_rightAnodyne
    q a b hb s₀ h₀

/-- 可変終点も元の初期時間辺の同じ全族のまま保持する。 -/
lemma specifiedCoconeRootVerticalInitialComparison_projection :
    (specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
        sliceUnderProjection v = fst T Δ[1] ≫ a ≫ sliceUnderProjection (r ≫ v) :=
  cosliceRetractionSectionComparison_projection v r s₁ h₁ endpointInclusion_rightAnodyne
    q a b hb s₀ h₀

/-- 比較の底の終点も、元の y の上で全時刻に固定する。 -/
lemma specifiedCoconeRootVerticalInitialComparison_fixed :
    ((specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y).h ≫
      sliceUnderProjection v) ≫ q = SSet.const y := by
  rw [specifiedCoconeRootVerticalInitialComparison_projection]
  have h := congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m)
    (specifiedCoconeRootVerticalInitialFamily_fixed hp p c hc dB dC y)
  simpa only [Category.assoc, SSet.comp_const] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
