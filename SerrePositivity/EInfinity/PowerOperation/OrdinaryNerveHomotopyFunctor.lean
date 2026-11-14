module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
# 対象と Hom の宇宙が異なる通常圏から元の nerve のホモトピー圏への関手

DAG XIII §2.2 の全始域比較の補助。元の対象と同じ通常射の辺の類を使う。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open scoped Simplicial

/-- 対象と同じ通常射の辺を、元の nerve の実ホモトピー圏へ送る。 -/
def ordinaryNerveHomotopyFunctor (C : Type u) [Category.{v} C] :
    C ⥤ hoFunctor.obj (nerve C) where
  obj x := HomotopyCategory.mk (nerveEquiv.symm x)
  map f := HomotopyCategory.homMk (nerve.edgeMk f)
  map_id x := by
    rw [nerve.edgeMk_id]
    exact HomotopyCategory.homMk_id _
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).mpr rfl
    exact (HomotopyCategory.homMk_comp_homMk h).symm

end SerrePositivity.EInfinity.PowerOperation
