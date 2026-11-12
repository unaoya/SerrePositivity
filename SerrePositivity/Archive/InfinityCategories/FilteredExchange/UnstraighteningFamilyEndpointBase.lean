module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism

/-!
概要：元の写像空間作用の普遍証拠の両端が被覆する底を同定する。
方針：同じ実 prism の始点・終点・射影条件を合成する。
規約：新しい持ち上げを選ばない。使われ方：指定比較の終点表示への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (t : K ⟶ leftUnstraighteningTransformationSpace F G)
local notation "E" => leftUnstraightening F
local notation "p" => leftUnstraighteningProjection F
local notation "d" => ((Δ[1] ◁ p) ▷ K) ≫
  functorParameterizedPrism (intervalMappingUncurry t)
local notation "w" => unstraighteningMappingFamilyWitness F G t

/-- 元の普遍証拠の始点の底は、同じ prism の零端点での評価。 -/
lemma unstraighteningMappingFamilyWitness_initial_base :
    (fst E K ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection =
      (prismEndpoint 0 E ▷ K) ≫ d := by
  rw [← UnstraighteningFamilyWitness.source w, Category.assoc,
    UnstraighteningFamilyWitness.projection w]

/-- 元の普遍証拠の終点の底は、元の終域図式の同じ族。 -/
lemma unstraighteningMappingFamilyWitness_final_base :
    (prismEndpoint 1 E ▷ K) ≫ d = (fst E K ≫ p) ≫ G := by
  rw [← UnstraighteningFamilyWitness.projection w, ← Category.assoc,
    UnstraighteningFamilyWitness.target w, Category.assoc, pullback.condition,
    ← Category.assoc]
  exact congrArg (fun r => r ≫ G)
    (relativeFunctorUncurry_projection (t ≫ leftUnstraighteningMappingSpaceMap F G))

end SerrePositivity.InfinityCategories.F2
