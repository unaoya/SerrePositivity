module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyPointedPrism
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningIdentityPrismData

/-!
概要：元の指定始域比較の一点制限の底・初期値・終点底を、同じ実始域射で回収する。
方針：元の普遍 prism の厳密な一致と、一点代入の二射影の式を使う。
規約：元の比較のデータを保持。使われ方：三証拠の直接比較と既存の指定比較の同定。
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
local notation "s₀" => s ≫ lift (𝟙 (leftUnstraightening F))
  (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))

/-- 元の一点制限の初期値は、同じ実始域射の pointed 成分そのもの。 -/
lemma functorHomotopyRestricted_initial :
    s₀ ≫ (fst (leftUnstraightening F) (Δ[0] : SSet.{u + 1}) ≫
      𝟙 (leftUnstraightening F) ≫ pullback.fst pointedSpaceProjection F) =
      s ≫ pullback.fst pointedSpaceProjection F := by
  simp only [Category.assoc, lift_fst_assoc, Category.id_comp]

/-- 元の一点制限の終点底は、同じ実始域射の元の射影。 -/
lemma functorHomotopyRestricted_apex :
    s₀ ≫ (fst (leftUnstraightening F) (Δ[0] : SSet.{u + 1}) ≫
      leftUnstraighteningProjection F) = s ≫ leftUnstraighteningProjection F := by
  simp only [Category.assoc, lift_fst_assoc, Category.id_comp]

/-- 同じ元の普遍 prism の射影は、元の指定比較の一点制限の底そのもの。 -/
lemma functorHomotopyRestricted_base :
    functorHomotopyPointedPrism H s ≫ pointedSpaceProjection =
    prismParameterRestriction s₀ ≫
      ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ (Δ[0] : SSet.{u + 1})) ≫
        functorParameterizedPrism (intervalMappingUncurry t) := by
  rw [functorHomotopyPointedPrism, Category.assoc, (functorHomotopyPointedWitness H).projection]
  rfl

/-- 元の指定始域比較の普遍 prism の一点制限は、同じ元の普遍 prism の実制限。 -/
lemma functorHomotopyRestricted_universal :
    prismParameterRestriction s₀ ≫
      (((Δ[1] ◁ 𝟙 (leftUnstraightening F)) ⊗ₘ (t : (Δ[0] : SSet.{u + 1}) ⟶ _)) ≫
        leftUnstraighteningTransformationFamilyLift F G) = functorHomotopyPointedPrism H s := by
  rw [unstraighteningIdentityPrism_eq F G (t : (Δ[0] : SSet.{u + 1}) ⟶ _)]
  rfl

end SerrePositivity.InfinityCategories.F2
