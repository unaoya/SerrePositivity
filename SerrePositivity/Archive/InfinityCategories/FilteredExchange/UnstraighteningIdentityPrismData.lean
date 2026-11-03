module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningIdentityPrism

/-!
概要：恒等始域の普遍 prism の端点と底を、元の族の同じ証拠から回収する。
方針：実 prism と終点の等式を元の証拠の三条件に適用する。
規約：全パラメータと実際の普遍的持ち上げを保持。
使われ方：三角形比較の実際の成分への始域制限公式の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} (F G : B ⟶ SpaceInfinity.{u})
  (t : K ⟶ leftUnstraighteningTransformationSpace F G)
local notation "A" => leftUnstraightening F
local notation "Z" => ((Δ[1] ◁ 𝟙 A) ⊗ₘ t) ≫ leftUnstraighteningTransformationFamilyLift F G
local notation "d" => ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  functorParameterizedPrism (intervalMappingUncurry t)
local notation "v" => fst A K ≫ 𝟙 A ≫ pullback.fst pointedSpaceProjection F
local notation "g" => (𝟙 A ⊗ₘ t) ≫ relativeFunctorUncurry (leftUnstraighteningMappingSpaceMap F G)

/-- 恒等始域での普遍 prism の底は元の指定変換の族。 -/
lemma unstraighteningIdentityPrism_projection : Z ≫ pointedSpaceProjection = d := by
  rw [unstraighteningIdentityPrism_eq]
  exact (unstraighteningMappingFamilyWitness F G t).projection

/-- 恒等始域での普遍 prism の始点は元の初期値。 -/
lemma unstraighteningIdentityPrism_source : (prismEndpoint 0 A ▷ K) ≫ Z = v := by
  rw [unstraighteningIdentityPrism_eq]
  simpa only [Category.id_comp] using (unstraighteningMappingFamilyWitness F G t).source

/-- 恒等始域の実際の終点の族は元の射影を被覆する。 -/
lemma unstraighteningIdentityFamily_projection :
    g ≫ leftUnstraighteningProjection G = fst A K ≫ leftUnstraighteningProjection F := by
  rw [unstraighteningIdentityFamily_eq]
  exact relativeFunctorUncurry_projection (t ≫ leftUnstraighteningMappingSpaceMap F G)

/-- 恒等始域での普遍 prism の終点は同じ比較射の実際の族。 -/
lemma unstraighteningIdentityPrism_target :
    (prismEndpoint 1 A ▷ K) ≫ Z = g ≫ pullback.fst pointedSpaceProjection G := by
  rw [unstraighteningIdentityPrism_eq, unstraighteningIdentityFamily_eq]
  exact (unstraighteningMappingFamilyWitness F G t).target

/-- 同じ普遍 prism の始点と底の可換性。 -/
lemma unstraighteningIdentityPrism_initial :
    v ≫ pointedSpaceProjection = (prismEndpoint 0 A ▷ K) ≫ d := by
  rw [← unstraighteningIdentityPrism_source F G t, Category.assoc,
    unstraighteningIdentityPrism_projection]

/-- 同じ普遍 prism の終点が元の標的図式を被覆する。 -/
lemma unstraighteningIdentityPrism_endpoint :
    (prismEndpoint 1 A ▷ K) ≫ d =
      (fst A K ≫ leftUnstraighteningProjection F) ≫ G := by
  rw [← unstraighteningIdentityPrism_projection F G t, ← Category.assoc,
    unstraighteningIdentityPrism_target, Category.assoc, pullback.condition,
    ← Category.assoc]
  exact congrArg (fun k => k ≫ G) (unstraighteningIdentityFamily_projection F G t)

end SerrePositivity.InfinityCategories.F2
