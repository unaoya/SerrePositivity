module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismDirectFiberOutput
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation

/-!
概要：旧 prism 関手の指定像を、同じ直接 fiber 評価による指定像の下降へ同定する。
方針：新旧の単体的写像の厳密な一致と下降の自然性を、端点等式を保持して合成する。
規約：元の指定同型を保持。使われ方：切断の終点比較と既存の模型 path の指定類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (q : (Δ[1] : SSet.{u + 1}) ⊗ coherentNativeTriangleFiberParameters F b ⟶ SpaceInfinity.{u})
  (hq₀ : coherentCospanFiberPointedSource F b ≫ pointedSpaceProjection =
    prismEndpoint 0 (coherentNativeTriangleFiberParameters F b) ≫ q)
  (hq₁ : prismEndpoint 1 (coherentNativeTriangleFiberParameters F b) ≫ q =
    ((smallUnstraighteningSourceRestriction F
      (vertexFiberι (smallLeftUnstraighteningProjection F) b)).left ≫
        leftUnstraighteningProjection F) ≫ J)
local notation "a" => coherentNativeTriangleFiberParameters F b
local notation "m" => smallUnstraighteningSourceRestriction F
  (vertexFiberι (smallLeftUnstraighteningProjection F) b)
local notation "c" => Over.Hom.left m ≫ leftUnstraighteningProjection F
local notation "src" => coherentCospanFiberPointedSource F b
local notation "E" => uliftFunctorSpaceIso
  (vertexFiber (smallLeftUnstraighteningProjection F) b)
  (vertexFiber (smallLeftUnstraighteningProjection J) b)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection J) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の任意の指定比較の旧出力は、同じ直接 fiber 評価の指定像を下降した値。 -/
lemma coherentPrismFiberFunctor_heq_direct
    {x y : (relativeFunctorExtensionSpace pointedSpaceProjection q
      (prismEndpoint 0 a) src hq₀) _⦋0⦌} (e : VertexIso x y) :
    HEq ((coherentPrismFiberFunctor F J b q hq₀ hq₁).mapIso e)
      (downVertexIso (VertexIso.map
        (VertexIso.map e (coherentPrismDirectFiberOutput F J b q hq₀ hq₁)) (E).inv)) := by
  let P := relativeFunctorExtensionEndpoint pointedSpaceProjection q (prismEndpoint 0 a)
    src hq₀ (prismEndpoint 1 a) J c hq₁
  let D := coherentPrismDirectFiberOutput F J b q hq₀ hq₁
  let L := coherentPrismFiberOutputLift F J b
  have hD : D = P ≫ L := coherentPrismDirectFiberOutput_eq F J b q hq₀ hq₁
  let ed := VertexIso.map e D
  let em := VertexIso.map (VertexIso.map e P) L
  have hm : HEq ed em := (vertexIso_map_heq e hD).trans
    (heq_of_eq (vertexIso_map_comp e P L).symm)
  have hx : D.app (Opposite.op ⦋0⦌) x = L.app _ (P.app _ x) :=
    congrArg (fun f => f.app (Opposite.op ⦋0⦌) x) hD
  have hy : D.app (Opposite.op ⦋0⦌) y = L.app _ (P.app _ y) :=
    congrArg (fun f => f.app (Opposite.op ⦋0⦌) y) hD
  have hi := vertexIso_map_heq_of_heq ed em hx hy hm (E).inv
  have hd := downVertexIso_heq_of_heq (VertexIso.map ed (E).inv) (VertexIso.map em (E).inv)
    (congrArg (fun z => (E).inv.app (Opposite.op ⦋0⦌) z) hx)
    (congrArg (fun z => (E).inv.app (Opposite.op ⦋0⦌) z) hy) hi
  exact (heq_of_eq (coherentPrismFiberFunctor_mapIso_output F J b q hq₀ hq₁ e)).trans
    ((coherentPrismFiberOutputFunctor_heq_down_lift F J b (VertexIso.map e P)).trans hd.symm)

end SerrePositivity.InfinityCategories.F2
