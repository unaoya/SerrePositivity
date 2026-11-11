module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UniverseHomotopyFaithful
/-!
概要：元の実頂点間のホモトピー圏 retract は任意の ULift 宇宙で同値な条件である。
方針：公開済みのホモトピー圏の持ち上げ・降下関手へ両射と分裂式を送る。
規約：頂点同型だけへ弱めず、元の二射の retract 式を保持する。
使われ方：D-16 追加 (3) の共通宇宙での厚い核の retract 表示。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial

lemma homotopyRetract_ulift_iff {X : SSet.{u}} (x y : X _⦋0⦌) :
    Nonempty (Retract
      (SSet.HomotopyCategory.mk (X := (SSet.uliftFunctor.{v}).obj X) (ULift.up x))
      (SSet.HomotopyCategory.mk (X := (SSet.uliftFunctor.{v}).obj X) (ULift.up y))) ↔
      Nonempty (Retract (SSet.HomotopyCategory.mk x) (SSet.HomotopyCategory.mk y)) :=
  ⟨fun ⟨r⟩ => ⟨r.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.universeHomotopyDown X)⟩,
    fun ⟨r⟩ => ⟨r.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.universeHomotopyUp X)⟩⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
