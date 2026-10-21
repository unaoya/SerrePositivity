module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopySourceComparison

/-!
概要：F1 の指定始域比較に使う普遍 prism と作用を、同じ実始域射の元の証拠へ揃える。
方針：普遍 prism の全成分を計算し、定値変換族の作用の厳密な表示を使う。
規約：元の全係数と選択済み作用を保持。使われ方：同じ指定始域比較の成分の照合。
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
  (H : SSet.Homotopy F G) (s : C ⟶ leftUnstraightening F)
local notation "t" => SSet.const (coherentVertexOfHomotopy H)

/-- F1 の同じ普遍 prism は、元の実始域で制限した同じ prism の一点パラメータ族。 -/
lemma functorHomotopySourceUniversalPrism_eq :
    ((Δ[1] ◁ s) ⊗ₘ (t : (Δ[0] : SSet.{u + 1}) ⟶ _)) ≫
      leftUnstraighteningTransformationFamilyLift F G =
    fst ((Δ[1] : SSet.{u + 1}) ⊗ C) Δ[0] ≫ functorHomotopyPointedPrism H s := by
  apply SSet.hom_ext
  intro n
  rfl

/-- F1 の同じ普遍作用は、元の実始域射の後の同じ選択済み作用の全族。 -/
lemma functorHomotopySourceUniversalMap_eq :
    (s ⊗ₘ (t : (Δ[0] : SSet.{u + 1}) ⟶ _)) ≫
      relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G) =
    fst C Δ[0] ≫ s ≫
      (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val := by
  have he : (s ⊗ₘ (t : (Δ[0] : SSet.{u + 1}) ⟶ _)) =
      (s ▷ Δ[0]) ≫ (leftUnstraightening F ◁ t) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [he, Category.assoc, ← relativeFunctorUncurry_naturality,
    unstraighteningMappingConst_uncurry, ← Category.assoc, whiskerRight_fst, Category.assoc]

end SerrePositivity.InfinityCategories.F2
