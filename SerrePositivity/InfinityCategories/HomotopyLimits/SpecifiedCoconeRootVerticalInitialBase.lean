module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalInitial

/-!
概要：同じ根辺円柱の初期時間図式上の全族の底が、時間に依存しないことを証明する。
方針：円柱全体の底の式を初期辺へ制限し、二つの形状の join の合成を照合する。
規約：全 Hom パラメータの厳密な等式。使われ方：定値な時間図式の二切断比較。
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
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "a" => specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y
local notation "hv" => specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 元の左長辺の底の同じ初期頂点上の全 Hom 係数。 -/
def specifiedCoconeRootVerticalInitialBaseFamily : T ⟶ sliceUnder (v ≫ q) :=
  (a ≫ sliceUnderPostcomp W q) ≫
    normalizedCoconeRestriction (W ≫ q) (stdSimplex.δ (1 : Fin 2))
      (by rw [← Category.assoc, hv])

/-- 初期側の全族の底は、同じ係数族の点への射影による引き戻しそのもの。 -/
lemma specifiedCoconeRootVerticalInitialFamily_base :
    specifiedCoconeRootVerticalInitialFamily hp p c hc dB dC y ≫
        sliceUnderPostcomp (r ≫ v) q =
      specifiedCoconeRootVerticalInitialBaseFamily hp p c hc dB dC y ≫
        sliceUnderRestrict (v ≫ q) r := by
  apply sliceUnderUncurry_injective ((r ≫ v) ≫ q)
  rw [sliceUnderUncurry_postcomp, specifiedCoconeRootVerticalInitialFamily,
    normalizedCoconeRestriction_uncurry, Category.assoc, ← sliceUnderUncurry_postcomp,
    specifiedCoconeRootVerticalFamily_base, normalizedCoconeRestriction_uncurry]
  rw [sliceUnderUncurry_restrict, specifiedCoconeRootVerticalInitialBaseFamily,
    normalizedCoconeRestriction_uncurry]
  rw [← Category.assoc (joinMap (prismEndpoint 0 Δ[1]) (𝟙 T))
      (joinMap (fst (Δ[1] : SSet.{u + 1}) Δ[1]) (𝟙 T)),
    ← joinMap_comp, Category.comp_id, initialPrismRetraction_fst]
  rw [← Category.assoc (joinMap r (𝟙 T)) (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T)),
    ← joinMap_comp, Category.comp_id]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
