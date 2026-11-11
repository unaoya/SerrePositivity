module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：半順序の順序双対の nerve を、元の圏の反対圏の nerve と同定する。
方針：順序双対の標準関手の順逆を nerve に移す。
規約：同値だけでなく、全頂点と全単体を保持する厳密な同型。
使われ方：有限 span の nerve 表示から有限 cospan の表示を得る。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 順序双対を反対圏として表示する全単体の同型。 -/
def orderDualNerveIso (P : Type u) [Preorder P] : nerve Pᵒᵈ ≅ nerve Pᵒᵖ where
  hom := nerveMap (orderDualEquivalence P).functor
  inv := nerveMap (orderDualEquivalence P).inverse
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.nerve.ext_of_isThin
    funext k
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.nerve.ext_of_isThin
    funext k
    rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
