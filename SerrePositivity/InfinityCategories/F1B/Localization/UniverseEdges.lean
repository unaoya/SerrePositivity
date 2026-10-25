module

public import SerrePositivity.InfinityCategories.Core.UniverseEdgeTransport
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization

/-!
概要：指定辺集合を反転する条件と宇宙持ち上げとの両方向の比較。
方針：同じ元の辺の像を上げ下げし、軽いホモトピー圏の関手で可逆性を移す。
規約：始域・標的の quasicategory 性は不要。辺集合は単なる ULift の像。
使われ方：局所化の普遍性を異なる宇宙で比較する際の最初の条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定した全辺の反転条件は、同じ射と辺集合の宇宙持ち上げで保存・反映される。 -/
lemma invertsEdges_ulift_iff {X D : SSet.{u}} (F : X ⟶ D) (W : Set (X _⦋1⦌)) :
    InvertsEdges ((SSet.uliftFunctor.{v, u}).map F) (ULift.up.{v, u} '' W) ↔
      InvertsEdges F W := by
  constructor
  · intro h s hs
    have hi := h (Set.mem_image_of_mem ULift.up hs)
    exact UniverseEdge.invertible_down hi
  · intro h s hs
    obtain ⟨s, hs, rfl⟩ := hs
    exact UniverseEdge.invertible_up (h hs)

end SerrePositivity.InfinityCategories
