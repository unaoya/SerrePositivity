module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopySourceUniversal

/-!
概要：F1 の指定始域比較の普遍 prism と作用の三条件を、同じ元の証拠から回収する。
方針：普遍 prism・作用の厳密な同定を、保持した一点パラメータの証拠へ渡す。
規約：指定成分を再選択しない。使われ方：既存の比較の各点成分の制限公式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B) (s : C ⟶ leftUnstraightening F)
  (hi : s ≫ leftUnstraighteningProjection F = p)
local notation "t" => SSet.const (coherentVertexOfHomotopy H)
local notation "Z" => ((Δ[1] ◁ s) ⊗ₘ (t : Δ[0] ⟶ _)) ≫
  leftUnstraighteningTransformationFamilyLift F G
local notation "g" => (s ⊗ₘ (t : Δ[0] ⟶ _)) ≫
  relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G)

include hi in
/-- F1 の同じ普遍 prism の底は、同じ元の指定変換の全図式。 -/
lemma functorHomotopySourceUniversal_projection :
    Z ≫ pointedSpaceProjection = ((Δ[1] ◁ p) ▷ (Δ[0] : SSet.{u + 1})) ≫
      functorParameterizedPrism (intervalMappingUncurry t) := by
  rw [functorHomotopySourceUniversalPrism_eq]
  exact functorHomotopySourceWrappedPrism_projection H p s
    (functorHomotopySourceCanonicalWitness H p s hi)

/-- F1 の同じ普遍 prism は、同じ元の実始域射の全初期値を保持する。 -/
lemma functorHomotopySourceUniversal_source :
    (prismEndpoint 0 C ▷ (Δ[0] : SSet.{u + 1})) ≫ Z =
      fst C Δ[0] ≫ s ≫ pullback.fst pointedSpaceProjection F := by
  rw [functorHomotopySourceUniversalPrism_eq]
  exact functorHomotopySourceWrappedPrism_source H (s ≫ leftUnstraighteningProjection F) s
    (functorHomotopySourceCanonicalWitness H (s ≫ leftUnstraighteningProjection F) s rfl)

include hi in
/-- F1 の同じ普遍作用は、元の全パラメータの底の射影を保つ。 -/
lemma functorHomotopySourceUniversalMap_projection :
    g ≫ leftUnstraighteningProjection G = fst C (Δ[0] : SSet.{u + 1}) ≫ p := by
  rw [functorHomotopySourceUniversalMap_eq]
  exact functorHomotopySourceWrappedMap_projection H p s
    (functorHomotopySourceCanonicalWitness H p s hi)

/-- F1 の同じ普遍 prism の終点は、元の同じ普遍作用の pointed 成分。 -/
lemma functorHomotopySourceUniversal_target :
    (prismEndpoint 1 C ▷ (Δ[0] : SSet.{u + 1})) ≫ Z = g ≫
      pullback.fst pointedSpaceProjection G := by
  rw [functorHomotopySourceUniversalPrism_eq, functorHomotopySourceUniversalMap_eq]
  exact functorHomotopySourceWrappedPrism_target H (s ≫ leftUnstraighteningProjection F) s
    (functorHomotopySourceCanonicalWitness H (s ≫ leftUnstraighteningProjection F) s rfl)

end SerrePositivity.InfinityCategories.F2
