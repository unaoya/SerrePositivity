module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentNativeModelComparisonTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUpperUnitTriangle

/-!
概要：元の二辺合成の模型単位終点を、同じ全三角形の単位交換の終点へ揃える。
方針：元の縮小の合成式と同じ全空間射の単位後合成を厳密に回収する。
規約：元の実二辺を保持。使われ方：模型三角形の指定値を既存の単位交換式へ代入する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "f₀₁" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "f₁₂" => Subtype.val (leftUnstraighteningMappingVertexMap G J
  (coherentVertexOfHomotopy b))
local notation "a₀" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy a)
local notation "b₀" => coherentTransformationTotalMap G J (coherentVertexOfHomotopy b)

/-- 元の二辺合成の模型終点は、同じ最後辺の単位終点を最初の実作用で前合成した射。 -/
lemma coherentTotalTriangleNativeModelTarget_eq_unit :
    (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F J (a₀ ≫ b₀)) =
    f₀₁ ≫ ((smallLeftUnstraighteningIso G).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (b₀ ≫ coherentDiagramTotalUnit J)) := by
  have h := congrArg (fun k => (smallLeftUnstraighteningIso F).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F J k))
    (smallSimplicialMap_comp.{u, u + 1} f₀₁ f₁₂).symm
  exact h.trans ((coherentNativeModel_smallMap_unit F J (f₀₁ ≫ f₁₂)).trans
    (coherentColimitUpperUnitTriangle_target (B := B) (a := a) (b := b)))

end SerrePositivity.InfinityCategories.F2
