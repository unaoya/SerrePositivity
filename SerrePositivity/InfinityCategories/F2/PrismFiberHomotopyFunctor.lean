module

public import SerrePositivity.InfinityCategories.F2.CoherentRestrictedPrismEndpoint
public import SerrePositivity.InfinityCategories.F2.SmallRestrictedTriangleEndpoint
public import SerrePositivity.InfinityCategories.F2.RelativeFiberRestriction
public import SerrePositivity.InfinityCategories.F2.UniverseHomotopyDownComposite

/-!
概要：始点固定 prism の指定類を、元の小さい fiber 間の関手の指定類へ写す関手。
方針：実終点評価・相対空間の縮小・宇宙下降・fiber Hom を一つのホモトピー圏の関手にする。
規約：元の射と指定同型を保持。使われ方：native 全錐と実際の fiber 比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
local notation "pF" => smallLeftUnstraighteningProjection F
local notation "pJ" => smallLeftUnstraighteningProjection J
local notation "i" => vertexFiberι pF b
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F i
local notation "c" => Over.Hom.left m ≫ leftUnstraighteningProjection F
local notation "src" => coherentCospanFiberPointedSource F b
local notation "R" => relativeFunctorSpace pJ (i ≫ pF)
local notation "Q" => relativeFunctorBaseFiberHom pJ (i ≫ pF) b (vertexFiberι_comp pF b)

/-- 実終点の大きい相対空間から、同じ小さい相対空間の宇宙持ち上げへの指定射。 -/
def coherentPrismEndpointShrink : relativeFunctorSpace (leftUnstraighteningProjection J) c ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj R :=
  eqToHom (congrArg (relativeFunctorSpace (leftUnstraighteningProjection J)) (m).w) ≫
    (smallUnstraighteningSourceRelativeIso J (i ≫ pF)).inv

/-- 元の prism の指定同型を、元の小さい fiber 間の関手のホモトピー圏へ写す。 -/
def coherentPrismFiberFunctor
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq₀ : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hq₁ : prismEndpoint 1 a ≫ q = c ≫ J) :
    (relativeFunctorExtensionSpace pointedSpaceProjection q
      (prismEndpoint 0 a) src hq₀).HomotopyCategory
      ⥤ ((ihom (vertexFiber pF b)).obj (vertexFiber pJ b)).HomotopyCategory :=
  SSet.mapHomotopyCategory
    (relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq₀
      (prismEndpoint 1 a) J c hq₁ ≫ coherentPrismEndpointShrink F J b) ⋙
    universeHomotopyDown R ⋙ SSet.mapHomotopyCategory Q

/-- この関手の指定同型への作用は、同じ終点・縮小・下降・fiber Hom の順次の指定像。 -/
lemma coherentPrismFiberFunctor_mapIso
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq₀ : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hq₁ : prismEndpoint 1 a ≫ q = c ≫ J)
    {x y : (relativeFunctorExtensionSpace pointedSpaceProjection q
      (prismEndpoint 0 a) src hq₀) _⦋0⦌} (e : VertexIso x y) :
    (coherentPrismFiberFunctor F J b q hq₀ hq₁).mapIso e =
      VertexIso.map (downVertexIso (VertexIso.map (VertexIso.map e
        (relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq₀
          (prismEndpoint 1 a) J c hq₁)) (coherentPrismEndpointShrink F J b))) Q :=
  universeHomotopyDown_composite_mapIso
    (relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq₀
      (prismEndpoint 1 a) J c hq₁) (coherentPrismEndpointShrink F J b) Q e

end SerrePositivity.InfinityCategories.F2
