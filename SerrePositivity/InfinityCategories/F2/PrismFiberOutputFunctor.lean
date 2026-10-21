module

public import SerrePositivity.InfinityCategories.F2.PrismFiberHomotopyFunctor

/-!
概要：実終点の後の縮小・宇宙下降・fiber Hom を同じ一つの関手として扱う。
方針：一般の下降の合成則を使い、全 prism の関手と終点後の関手の指定像を照合する。
規約：同じ元の射と指定値を保持。使われ方：終点の両端補正と左右合成の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
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

/-- 元の実終点を同じ小さい fiber の関手へ写す、縮小・下降・fiber Hom の関手。 -/
def coherentPrismFiberOutputFunctor :
    (relativeFunctorSpace (leftUnstraighteningProjection J) c).HomotopyCategory ⥤
      ((ihom (vertexFiber pF b)).obj (vertexFiber pJ b)).HomotopyCategory :=
  SSet.mapHomotopyCategory (coherentPrismEndpointShrink F J b) ⋙
    universeHomotopyDown R ⋙ SSet.mapHomotopyCategory Q

/-- この関手の指定像は元の縮小・下降・fiber Hom の順次の指定像。 -/
lemma coherentPrismFiberOutputFunctor_mapIso
    {x y : (relativeFunctorSpace (leftUnstraighteningProjection J) c) _⦋0⦌}
    (e : VertexIso x y) :
    (coherentPrismFiberOutputFunctor F J b).mapIso e =
      VertexIso.map (downVertexIso (VertexIso.map e (coherentPrismEndpointShrink F J b))) Q :=
  universeHomotopyDown_post_mapIso (coherentPrismEndpointShrink F J b) Q e

/-- prism の全関手の指定像は、同じ実終点像を終点後の関手へ写した値。 -/
lemma coherentPrismFiberFunctor_mapIso_output
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq₀ : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hq₁ : prismEndpoint 1 a ≫ q = c ≫ J)
    {x y : (relativeFunctorExtensionSpace pointedSpaceProjection q
      (prismEndpoint 0 a) src hq₀) _⦋0⦌} (e : VertexIso x y) :
    (coherentPrismFiberFunctor F J b q hq₀ hq₁).mapIso e =
      (coherentPrismFiberOutputFunctor F J b).mapIso (VertexIso.map e
        (relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq₀
          (prismEndpoint 1 a) J c hq₁)) :=
  (coherentPrismFiberFunctor_mapIso F J b q hq₀ hq₁ e).trans
    (coherentPrismFiberOutputFunctor_mapIso F J b _).symm

/-- 元の prism の実頂点の像は、同じ実終点・縮小・下降・fiber Hom の実頂点。 -/
lemma coherentPrismFiberFunctor_obj_vertex
    (q : (Δ[1] : SSet.{u + 1}) ⊗ a ⟶ SpaceInfinity.{u})
    (hq₀ : src ≫ pointedSpaceProjection = prismEndpoint 0 a ≫ q)
    (hq₁ : prismEndpoint 1 a ≫ q = c ≫ J)
    (x : (relativeFunctorExtensionSpace pointedSpaceProjection q
      (prismEndpoint 0 a) src hq₀) _⦋0⦌) :
    (coherentPrismFiberFunctor F J b q hq₀ hq₁).obj (SSet.HomotopyCategory.mk x) =
      SSet.HomotopyCategory.mk ((Q).app (Opposite.op ⦋0⦌)
        (((coherentPrismEndpointShrink F J b).app (Opposite.op ⦋0⦌)
          ((relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a) src hq₀
            (prismEndpoint 1 a) J c hq₁).app (Opposite.op ⦋0⦌) x)).down)) := rfl

end SerrePositivity.InfinityCategories.F2
