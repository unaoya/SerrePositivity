module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseEdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-!
概要：指定辺集合を反転する条件と宇宙持ち上げとの両方向の比較。
方針：同じ元の辺の像を上げ下げし、軽いホモトピー圏の関手で可逆性を移す。
規約：始域・標的の quasicategory 性は不要。辺集合は単なる ULift の像。
使われ方：局所化の普遍性を異なる宇宙で比較する際の最初の条件。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 指定した全辺の反転条件は、同じ射と辺集合の宇宙持ち上げで保存・反映される。 -/
lemma invertsEdges_ulift_iff {X D : SSet.{u}} (F : X ⟶ D) (W : Set (X _⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((SSet.uliftFunctor.{v, u}).map F) (ULift.up.{v, u} '' W) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W := by
  constructor
  · intro h s hs
    have hi := h (Set.mem_image_of_mem ULift.up hs)
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.invertible_down hi
  · intro h s hs
    obtain ⟨s, hs, rfl⟩ := hs
    exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.invertible_up (h hs)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
