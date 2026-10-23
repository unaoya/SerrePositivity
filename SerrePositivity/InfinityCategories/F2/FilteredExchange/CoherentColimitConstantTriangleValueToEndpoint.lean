module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorSequentialPostFiberMapVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitConstantTriangleValueTo
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitLowerValueToCancellation

/-!
概要：元の定値三角形因子の固定値への終点を、同じ実二辺作用の頂点として計算する。
方針：元の三つの相対後合成を同じ実合成射へ戻して fiber 射影を計算する。
規約：指定二辺と元の単位を保持。使われ方：五因子式の三角形因子の厳密な消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => leftUnstraighteningProjection F
local notation "z₀" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z₁" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "z₃" => JoinCocone.vertex (coherentDiagramTotalCocone J)
local notation "uF" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "x₀" => relativeFunctorVertex p p (𝟙 (leftUnstraightening F)) (Category.id_comp p)
local notation "ca" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)
local notation "cb" => simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B b)
local notation "ma" => leftUnstraighteningMappingVertexMap (SSet.const z₀) (SSet.const z₁)
  (coherentVertexOfHomotopy ca)
local notation "mb" => leftUnstraighteningMappingVertexMap (SSet.const z₁) (SSet.const z₃)
  (coherentVertexOfHomotopy cb)
local notation "u₀" => leftUnstraighteningMappingVertexMap F (SSet.const z₀)
  (coconeTransformationVertex (coherentDiagramTotalCocone F))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "Q" => constantTargetValueProjectionTo p (coherentDiagramTotalCocone_vertex J)

omit T in
/-- 元の定値二辺と元の単位の指定終点は、同じ実二辺合成の固定値への頂点。 -/
lemma coherentColimitConstantTriangleValueTo_target_vertex :
    NatTrans.app Q (Opposite.op ⦋0⦌)
      ((functorHomotopyRelativePost cb p).app (Opposite.op ⦋0⦌)
        ((functorHomotopyRelativePost ca p).app (Opposite.op ⦋0⦌)
          ((functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀))) =
      functorVertex ((Subtype.val u₀ ≫ ((Subtype.val ma ≫ Subtype.val mb) ≫
        constantUnstraighteningFiberProjection
          (CategoryTheory.Functor.obj SSet.uliftFunctor B) z₃)) ≫ V) := by
  let v := leftUnstraighteningMappingVertexMap F (SSet.const z₀) (coherentVertexOfHomotopy uF)
  have hx : (functorHomotopyRelativePost uF p).app (Opposite.op ⦋0⦌) x₀ =
      relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z₀)) p
        (Subtype.val v) (Subtype.property v) := by
    apply Subtype.ext
    rfl
  rw [constantTargetValueProjectionTo_eq_fiberValueTo, hx]
  have h := functorSequentialPost_fiberMap_vertex ca cb p
    (Subtype.val v) (Subtype.property v) V
  simpa only [v, coherentVertexOfHomotopy_cocone, Category.assoc] using h

end SerrePositivity.InfinityCategories.F2
