module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalInitialComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalStart
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootVerticalEnd

/-!
概要：定値な初期時間辺の二端を、同じ円柱の元の時間零・一の端面の初期値へ同定する。
方針：同じ正方形の頂点の等式を join の uncurry に移し、比較円柱を表示し直す。
規約：元の全族と raw な円柱を保持する。使われ方：左右の初期 Hom 族の全作用の比較。
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
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫
  specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "V" => tetrahedronRootEdge ≫ specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "hW" => specifiedCoconeRootClosingLeft_initial hp p c hc dB dC
local notation "hV" => specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC
local notation "P₀" => normalizedCoconeRestriction (r ≫ v) (stdSimplex.δ (1 : Fin 2))
  (cosliceRetractionFamily_diagram v r (stdSimplex.δ (1 : Fin 2))
    (intervalRetraction_endpoint (1 : Fin 2)))
local notation "P₁" => normalizedCoconeRestriction (r ≫ v) (stdSimplex.δ (0 : Fin 2))
  (cosliceRetractionFamily_diagram v r (stdSimplex.δ (0 : Fin 2))
    (intervalRetraction_endpoint (0 : Fin 2)))
local notation "F₀" => specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y ≫
  normalizedCoconeRestriction W (stdSimplex.δ (1 : Fin 2)) hW
local notation "F₁" => specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫
  normalizedCoconeRestriction V (stdSimplex.δ (1 : Fin 2)) hV
local notation "H" => specifiedCoconeRootVerticalInitialComparison hp p c hc dB dC y
local notation "U" => specifiedCoconeRootVerticalFamily hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 定値な初期時間辺の時間零は、元の時間零の端面の初期制限そのもの。 -/
lemma specifiedCoconeRootVerticalInitialFamily_zero : a ≫ P₀ = F₀ := by
  apply sliceUnderUncurry_injective v
  rw [normalizedCoconeRestriction_uncurry, specifiedCoconeRootVerticalInitialFamily,
    normalizedCoconeRestriction_uncurry, normalizedCoconeRestriction_uncurry,
    specifiedCoconeRootVerticalStartFamily, normalizedCoconeRestriction_uncurry]
  rw [← Category.assoc (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T))
      (joinMap (prismEndpoint 0 Δ[1]) (𝟙 T)) (sliceUnderUncurry U),
    ← joinMap_comp, Category.comp_id, initialPrismRetraction_zero,
    ← Category.assoc (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T))
      (joinMap SSet.ι₀ (𝟙 T)) (sliceUnderUncurry U),
    ← joinMap_comp, Category.comp_id]

/-- 定値な初期時間辺の時間一も、元の時間一の端面の初期制限そのもの。 -/
lemma specifiedCoconeRootVerticalInitialFamily_one : a ≫ P₁ = F₁ := by
  apply sliceUnderUncurry_injective v
  rw [normalizedCoconeRestriction_uncurry, specifiedCoconeRootVerticalInitialFamily,
    normalizedCoconeRestriction_uncurry, normalizedCoconeRestriction_uncurry,
    specifiedCoconeRootVerticalEndFamily, normalizedCoconeRestriction_uncurry]
  rw [← Category.assoc (joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 T))
      (joinMap (prismEndpoint 0 Δ[1]) (𝟙 T)) (sliceUnderUncurry U),
    ← joinMap_comp, Category.comp_id, initialPrismRetraction_one,
    ← Category.assoc (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 T))
      (joinMap SSet.ι₁ (𝟙 T)) (sliceUnderUncurry U),
    ← joinMap_comp, Category.comp_id]

/-- 同じ初期辺の比較円柱を、元の二つの時間端面の初期値の間で保持する。 -/
def specifiedCoconeRootVerticalInitialFaceComparison : SSet.Homotopy F₀ F₁ where
  h := (H).h
  h₀ := by
    change SSet.ι₀ ≫ (H).h = F₀
    exact (H).h₀.trans (specifiedCoconeRootVerticalInitialFamily_zero hp p c hc dB dC y)
  h₁ := by
    change SSet.ι₁ ≫ (H).h = F₁
    exact (H).h₁.trans (specifiedCoconeRootVerticalInitialFamily_one hp p c hc dB dC y)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 端面の表示を変えても、元の同じ初期比較円柱の raw な射を保持する。 -/
lemma specifiedCoconeRootVerticalInitialFaceComparison_raw :
    (specifiedCoconeRootVerticalInitialFaceComparison hp p c hc dB dC y).h = (H).h := rfl

/-- 端面表示でも底の初期 Hom 係数は全時刻固定する。 -/
lemma specifiedCoconeRootVerticalInitialFaceComparison_base :
    (specifiedCoconeRootVerticalInitialFaceComparison hp p c hc dB dC y).h ≫
        sliceUnderPostcomp v q = fst T Δ[1] ≫ F₀ ≫ sliceUnderPostcomp v q := by
  have h := specifiedCoconeRootVerticalInitialComparison_base hp p c hc dB dC y
  exact h.trans (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m ≫
    sliceUnderPostcomp v q) (specifiedCoconeRootVerticalInitialFamily_zero hp p c hc dB dC y))

end
end SerrePositivity.InfinityCategories.HomotopyLimits
