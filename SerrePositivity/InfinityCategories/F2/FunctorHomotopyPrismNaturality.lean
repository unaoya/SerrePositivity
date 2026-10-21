module

public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyPrismComparison

/-!
概要：始点も動く全 prism の普遍持ち上げと元の実 prism を、始点上で比較する。
方針：始点評価の厳密な切断と全境界持ち上げから、同じ fiber 内の全関手同型を取る。
規約：元の切断と実終点を保持。使われ方：共有辺の指定比較の全自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}}
  (H : SSet.Homotopy F G) (p : C ⟶ B)
local notation "d" => (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry H.h)
local notation "L" => relativeFunctorSpace pointedSpaceProjection d
local notation "q" => functorHomotopyPrismSourceEvaluation H p
local notation "r" => functorHomotopyPrismTargetEvaluation H p
local notation "s" => functorHomotopyPrismSection H p

local notation "f" => q ≫ HomotopyLimits.relativeFunctorPost (leftUnstraighteningProjection F)
  (leftUnstraighteningProjection G)
  (Subtype.val (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)))
  (Subtype.property (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H))) p
local notation "e" => functorHomotopyPrismEndpointComparison H p

/-- 始点も動く元の二つの全 prism の比較は、同じ native 作用と実終点で自然。 -/
lemma functorHomotopyPrismEndpointComparison_naturality {x y : L _⦋0⦌} (a : VertexIso x y) :
    VertexIso.map a f ≪≫ (e).app y = (e).app x ≪≫ VertexIso.map a r := by
  apply Iso.ext
  exact (e).toNatIso.hom.naturality a.hom

end SerrePositivity.InfinityCategories.F2
