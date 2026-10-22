module

public import SerrePositivity.InfinityCategories.F2.Ind.TwistedArrowSourceLift
public import SerrePositivity.InfinityCategories.F1.PresheafUnstraightening

/-!
概要：元の前層の小さい元の圏を終点とする全 twisted arrow を、同じ前層の値へ評価する。
方針：相対 twisted arrow の一つの切断の左端を、元の pointed-space 表示へ写す。
規約：一つの全単体の射と、その底の厳密な等式を保持する。
使われ方：元の Yoneda の共同 Hom 図式から元の F への大域比較の組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "p" => smallRightUnstraighteningProjection F

/-- 元の小さい元の圏を終点とする、全 twisted arrow の族。 -/
def presheafTwistedElements : SSet.{u} := pullback (edgewiseRight C) p

/-- 同じ前層の値への、全高次に整合する pointed 評価。 -/
def presheafTwistedElementsEvaluation :
    (SSet.uliftFunctor.{u + 1, u}).obj (presheafTwistedElements F) ⟶ PointedSpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map
      (twistedArrowSourceLift p ≫ (smallRightUnstraighteningOppositeIso F).hom) ≫
    (smallLeftUnstraighteningIso F).hom ≫ pullback.fst pointedSpaceProjection F

/-- 元の小さい全空間の反転を戻した左端評価も、指定した同じ反転した底を保つ。 -/
lemma presheafTwistedElements_source_projection :
    (twistedArrowSourceLift p ≫ (smallRightUnstraighteningOppositeIso F).hom) ≫
      smallLeftUnstraighteningProjection F = pullback.fst (edgewiseRight C) p ≫ edgewiseLeft C := by
  rw [Category.assoc, ← smallRightUnstraighteningProjection_op, twistedArrowSourceLift_projection]

/-- 同じ pointed 評価の底は、元の twisted arrow の始点で評価した元の F そのもの。 -/
lemma presheafTwistedElementsEvaluation_projection :
    presheafTwistedElementsEvaluation F ≫ pointedSpaceProjection =
      (SSet.uliftFunctor.{u + 1, u}).map
        (pullback.fst (edgewiseRight C) p ≫ edgewiseLeft C) ≫ F := by
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map
        (twistedArrowSourceLift p ≫ (smallRightUnstraighteningOppositeIso F).hom) ≫
        ((smallLeftUnstraighteningIso F).hom ≫ leftUnstraighteningProjection F) ≫ F := by
      simp only [presheafTwistedElementsEvaluation, leftUnstraighteningProjection,
        Category.assoc, pullback.condition]
    _ = _ := by
      rw [smallLeftUnstraighteningIso_projection, ← Category.assoc, ← Functor.map_comp,
        presheafTwistedElements_source_projection]

end SerrePositivity.InfinityCategories.F2.Ind
