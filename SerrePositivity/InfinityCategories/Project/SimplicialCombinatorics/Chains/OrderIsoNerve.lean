module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.Preorder

/-!
概要：元の順序同型を、元の全点と全射を保つ nerve の同型へ移す。
方針：順射・逆射を全ての単体へ作用させる。
規約：P の版との準重複はコーディネータの許可による。第 I 段終了時に R が統合する。
使われ方：Ind の点除去前後の固定部分と余錐形状の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
/-- 概要：元の順序同型の順逆写像を全単体へ移す。
方針：全点と射の比較。規約：元の順射。使われ方：部分型の形状同型。 -/
def orderIsoNerveIso {P Q : Type u} [Preorder P] [Preorder Q] (e : P ≃o Q) :
    nerve P ≅ nerve Q where
  hom := nerveMap e.monotone.functor
  inv := nerveMap e.symm.monotone.functor
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ e.symm_apply_apply _) (fun _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ e.apply_symm_apply _) (fun _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
