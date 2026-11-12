module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness

/-! # 始対象間の指定された辺の同型性

概要：二つの始対象の間の任意の辺のホモトピー類は同型となる。
方針：指定辺の片側逆を二回構成し、両側逆へ変える。
規約：quasicategory 性を仮定する。使われ方：cofiber 比較辺の擬同型性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet SSet.Truncated
open scoped _root_.Simplicial

/-- 始対象間の指定辺を順射とする同型。 -/
def initialEdgeIso {X : SSet.{u}} [SSet.Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex y)
    (f : SSet.Truncated.Edge (X := (SSet.truncation 2).obj X) x y) :
    HomotopyCategory₂.mk (A := (SSet.truncation 2).obj X) x ≅ HomotopyCategory₂.mk y := by
  let sg := Classical.choice (hy.nonempty_split f)
  let g := sg.1
  let sk := Classical.choice (hx.nonempty_split g)
  let k := sk.1
  have hg : HomotopyCategory₂.homMk g ≫ HomotopyCategory₂.homMk f =
      𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) y) := sg.2.homotopyCategory₂_fac
  have hk : HomotopyCategory₂.homMk k ≫ HomotopyCategory₂.homMk g =
      𝟙 (HomotopyCategory₂.mk (A := (truncation 2).obj X) x) := sk.2.homotopyCategory₂_fac
  have hf : HomotopyCategory₂.homMk f = HomotopyCategory₂.homMk k := by
    calc
      _ = (HomotopyCategory₂.homMk k ≫ HomotopyCategory₂.homMk g) ≫
          HomotopyCategory₂.homMk f := by rw [hk, Category.id_comp]
      _ = HomotopyCategory₂.homMk k ≫ (HomotopyCategory₂.homMk g ≫
          HomotopyCategory₂.homMk f) := Category.assoc _ _ _
      _ = HomotopyCategory₂.homMk k := by rw [hg, Category.comp_id]
  exact ⟨HomotopyCategory₂.homMk f, HomotopyCategory₂.homMk g, by rw [hf]; exact hk, hg⟩

/-- 始対象間の任意の辺のホモトピー類は同型射。 -/
lemma isIso_homMk_of_initial {X : SSet.{u}} [SSet.Quasicategory X] {x y : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex y)
    (f : SSet.Truncated.Edge (X := (SSet.truncation 2).obj X) x y) :
    IsIso (HomotopyCategory₂.homMk f) := by
  change IsIso (initialEdgeIso hx hy f).hom
  infer_instance

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
