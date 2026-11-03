module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge
public import SerrePositivity.InfinityCategories.F1.Compact.CoconeFiberPrism
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberTransport
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationPrismTransport

/-!
概要：元の余錐の fiber 写像を指定値に制限すると、同じ元の余錐脚に沿う輸送になる。
方針：元の実 prism を指定 fiber の包含へ制限し、同じ底の辺の輸送一意性を適用する。
規約：元の同じ fiber 写像と元の脚の全辺を保持。
使われ方：空間値余極限の点回収と、元の Hom 後合成との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の値の pointed fiber を、元の同じ unstraightening の全空間へ含める。 -/
def coconeLegFiberSource (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b) ⟶ leftUnstraightening F :=
  (leftUnstraighteningFiberIso F b).inv ≫ vertexFiberι (leftUnstraighteningProjection F) b

/-- 元の fiber 同型の順方向を戻して含めると、元の同じ fiber 包含そのもの。 -/
lemma coconeLegFiberSource_hom (b : B _⦋0⦌) :
    (leftUnstraighteningFiberIso F b).hom ≫ coconeLegFiberSource F b =
      vertexFiberι (leftUnstraighteningProjection F) b := by
  rw [coconeLegFiberSource, Iso.hom_inv_id_assoc]

/-- 元の指定値への包含は、同じ pointed fiber の包含を回収する。 -/
lemma coconeLegFiberSource_pointed (b : B _⦋0⦌) :
    coconeLegFiberSource F b ≫ pullback.fst pointedSpaceProjection F =
      vertexFiberι pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b) := by
  rw [coconeLegFiberSource, Category.assoc, leftUnstraighteningFiberIso_inv_ι_fst]

/-- 元の指定値の包含の底は、同じ元の頂点に厳密に定値。 -/
lemma coconeLegFiberSource_projection (b : B _⦋0⦌) :
    coconeLegFiberSource F b ≫ leftUnstraighteningProjection F = SSet.const b := by
  rw [coconeLegFiberSource, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 元の同じ余錐の fiber 写像そのものを、指定した元の値へ制限する。 -/
def coconeLegFiberMap (c : JoinCocone F) (b : B _⦋0⦌) :
    vertexFiber pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b) ⟶
      vertexFiber pointedSpaceProjection c.vertex :=
  coconeLegFiberSource F b ≫ coconeFiberMap c

/-- 元の実 fiber 写像の同じ指定値への制限は、元の余錐脚の実輸送と全自然同型。 -/
def coconeLegFiberMap_transportIso (c : JoinCocone F) (b : B _⦋0⦌) :
    FunctorIso (coconeLegFiberMap c b)
      (edgeTransport pointedSpaceProjection (coconeTransportLeg c b)) := by
  let H := (Δ[1] ◁ coconeLegFiberSource F b) ≫ coconeFiberPrism c
  have h₀ : prismEndpoint 0 _ ≫ H = (𝟙 _) ≫
      vertexFiberι pointedSpaceProjection (F.app (Opposite.op ⦋0⦌) b) := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      coconeFiberPrism_zero, coconeLegFiberSource_pointed, Category.id_comp]
  have h₁ : prismEndpoint 1 _ ≫ H =
      coconeLegFiberMap c b ≫ vertexFiberι pointedSpaceProjection c.vertex := by
    dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, coconeFiberPrism_one]
    rfl
  have hp : H ≫ pointedSpaceProjection =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) _ ≫
        SSet.yonedaEquiv.symm (coconeTransportLeg c b).edge := by
    dsimp only [H]
    rw [Category.assoc, coconeFiberPrism, unstraighteningVertexPrism_projection,
      ← Category.assoc, ← whiskerLeft_comp, coconeLegFiberSource_projection,
      functorEdgePrism_const]
    rfl
  simpa only [Category.id_comp] using
    leftFibrationPrism_transportIso pointedSpaceProjection (coconeTransportLeg c b)
      (𝟙 _) (coconeLegFiberMap c b) H h₀ h₁ hp

end SerrePositivity.InfinityCategories.F2.Compact
