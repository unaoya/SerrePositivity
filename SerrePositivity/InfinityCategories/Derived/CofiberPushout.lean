module
public import SerrePositivity.InfinityCategories.Derived.CofiberBoundaryJoinFaces

/-! # 標準 cofiber 余錐の普遍性

概要：複体の dg nerve における標準 cofiber 正方形が押し出しであることを証明する。
方針：指定余錐を最初の頂点に持つ全ての coslice 境界を、二セルの明示解で直接充填する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：D(S) の cofiber と安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S] {A B C : Complex S}

/-- 標準 cofiber 余錐は coslice の始対象である。 -/
lemma standardCofiberCocone_isColimit (f : A ⟶ B) (g : A ⟶ C) :
    IsColimitCone (standardCofiberCocone f g) := by
  intro n b hb
  let F := cofiberBoundaryJoinFiller f g b hb
  have hfaces := cofiberBoundaryJoinFiller_faces f g b hb
  refine ⟨sliceUnderCurry F (cosliceJoinBoundaryFaces_fixed _ b F hfaces), ?_⟩
  exact sliceUnderCurry_boundary_of_joinFaces _ b F hfaces

/-- 標準 mapping cone による cofiber 正方形は実際の ∞ 押し出しである。 -/
lemma standardCofiberSquare_isPushout (f : A ⟶ B) (g : A ⟶ C) :
    IsPushoutSquare (standardCofiberSquare f g) :=
  standardCofiberCocone_isColimit f g

end SerrePositivity.InfinityCategories
