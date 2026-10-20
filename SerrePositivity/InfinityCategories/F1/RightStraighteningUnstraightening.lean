module

public import SerrePositivity.InfinityCategories.F1.RightStraighteningInfinityEquivalence

/-!
概要：前層による同じ right fibration 分類と、既存の小さい right unstraightening の照合。
方針：共通解像の単位で指定した反転射影を回収し、二重反転の同型と左の余単位を使う。
規約：元の分類写像の逆は実際の ∞ 関手。既存の全空間との一致は頂点の同型で述べる。
使われ方：F1-2 の分類の逆関手が、指定した小さい right fibration を復元すること。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ分類写像は既存の小さい right unstraightening から元の前層を回収する。 -/
def rightStraighteningInfinityCounitVertex {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ SpaceInfinity.{u}) :
    VertexIso
      ((rightStraighteningInfinityMap B).app _
        (rightFibrationInfinityVertex (smallRightUnstraighteningProjection F)))
      (functorVertex F) := by
  let p := smallRightUnstraighteningProjection F
  have h₀ := VertexIso.map
    (rightFibrationOppositeInfinityVertexIso (rightFibrationObjectOf p))
    (leftStraighteningInfinityMap B.op)
  have h₁ := leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    (SSet.opFunctor.map p) (smallLeftUnstraighteningProjection F)
    (smallRightUnstraighteningOppositeIso F).hom
    (smallRightUnstraighteningProjection_op F).symm
    (isPrecompositionEquivalence_of_iso (smallRightUnstraighteningOppositeIso F))
  exact h₀ ≪≫ VertexIso.map h₁ (leftStraighteningInfinityMap B.op) ≪≫
    leftStraighteningInfinityCounitVertex F

/-- 元の前層 ∞ 圏から元の right fibration の ∞ 圏への unstraightening ∞ 関手。 -/
def rightUnstraighteningInfinityMap (B : SSet.{u}) [Quasicategory B] :
    PresheafInfinity B ⟶ RightFibrationInfinity B :=
  (rightStraighteningInfinityEquivalence B).inv

/-- 同じ unstraightening ∞ 関手は圏同値。 -/
lemma rightUnstraighteningInfinityMap_isQCatEquivalence (B : SSet.{u}) [Quasicategory B] :
    IsQCatEquivalence (rightUnstraighteningInfinityMap B) :=
  (rightStraighteningInfinityEquivalence B).symm.isQCatEquivalence

/-- 逆の ∞ 関手の前層 F での値は、指定した元の小さい right unstraightening と同型。 -/
def rightUnstraighteningInfinityVertexIso {B : SSet.{u}} [Quasicategory B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ SpaceInfinity.{u}) :
    VertexIso ((rightUnstraighteningInfinityMap B).app _ (functorVertex F))
      (rightFibrationInfinityVertex (smallRightUnstraighteningProjection F)) :=
  VertexIso.map (rightStraighteningInfinityCounitVertex F).symm
      (rightUnstraighteningInfinityMap B) ≪≫
    (rightStraighteningInfinityEquivalence B).homInvIso.app
      (rightFibrationInfinityVertex (smallRightUnstraighteningProjection F))

end SerrePositivity.InfinityCategories
