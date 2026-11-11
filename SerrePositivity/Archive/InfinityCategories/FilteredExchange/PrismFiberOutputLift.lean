module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PrismFiberOutputFunctor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseDownMappedIsoCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace

/-!
概要：既存の prism 出力を、元の fiber の持ち上げの関手空間への一つの単体的写像に表示する。
方針：縮小と fiber Hom を持ち上げて合成し、関手空間の宇宙同型の後で下降を比較する。
規約：指定同型の値を保持。使われ方：明示した pointed fiber 評価との厳密な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
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
local notation "R" => relativeFunctorSpace pJ (i ≫ pF)
local notation "Q" => relativeFunctorBaseFiberHom pJ (i ≫ pF) b (vertexFiberι_comp pF b)
local notation "E" => uliftFunctorSpaceIso (vertexFiber pF b) (vertexFiber pJ b)
local instance : KanComplex (vertexFiber pJ b) := vertexFiber_kanComplex_of_leftFibration _ _

/-- 旧出力の全行程を、持ち上げた元の fiber 間の関手空間への実際の写像に表示する。 -/
def coherentPrismFiberOutputLift : relativeFunctorSpace (leftUnstraighteningProjection J) c ⟶
    (ihom a).obj (coherentNativeTriangleFiberParameters J b) :=
  coherentPrismEndpointShrink F J b ≫ (SSet.uliftFunctor.{u + 1, u}).map Q ≫ (E).hom

/-- 表示同型の逆の後の写像は、縮小と持ち上げた fiber Hom の同じ合成である。 -/
lemma coherentPrismFiberOutputLift_inv :
    coherentPrismFiberOutputLift F J b ≫ (E).inv =
      coherentPrismEndpointShrink F J b ≫ (SSet.uliftFunctor.{u + 1, u}).map Q := by
  simp only [coherentPrismFiberOutputLift, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 旧出力関手の指定像は、この単体的写像による同じ指定像を戻して下降した値。 -/
lemma coherentPrismFiberOutputFunctor_heq_down_lift
    {x y : (relativeFunctorSpace (leftUnstraighteningProjection J) c) _⦋0⦌}
    (e : VertexIso x y) :
    HEq ((coherentPrismFiberOutputFunctor F J b).mapIso e)
      (downVertexIso (VertexIso.map
        (VertexIso.map e (coherentPrismFiberOutputLift F J b)) (E).inv)) := by
  exact (heq_of_eq (coherentPrismFiberOutputFunctor_mapIso F J b e)).trans
    (downVertexIso_map_iso_cancel (coherentPrismEndpointShrink F J b) Q E e)

end SerrePositivity.InfinityCategories.F2
