module

public import SerrePositivity.InfinityCategories.F2.FunctorVertexConeReindex

/-!
概要：coherent な錐の関手頂点表示から元の極限性を読み戻す。
方針：元の錐全体の等号から固定図式の等号を導き、slice の極限判定を移す。
規約：図式側の表示の等号も保持。使われ方：部分形状の極限錐の coherent な族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全錐を表す関手頂点から読み戻した錐は、同じ極限性を持つ。 -/
lemma isLimitCone_functorVertexCone_iff_of_val {J X : SSet.{u}} {p : J ⟶ X}
    (c : JoinCone p) (v : ((ihom (join (Δ[0] : SSet.{u}) J)).obj X) _⦋0⦌)
    (hv : functorVertexConeMap v = c.val) :
    IsLimitCone (functorVertexCone v) ↔ IsLimitCone c := by
  let d := functorVertexCone v
  have hp := d.property.symm.trans
    ((congrArg (fun k => joinInr (Δ[0] : SSet.{u}) J ≫ k) hv).trans c.property)
  exact isLimitCone_iff_of_diagram_eq hp hv

/-- 元の錐の関手頂点表示の往復は、その錐の極限性を保つ。 -/
lemma isLimitCone_functorVertexCone_functorVertex {J X : SSet.{u}} {p : J ⟶ X}
    (c : JoinCone p) :
    IsLimitCone (functorVertexCone (functorVertex c.val)) ↔ IsLimitCone c :=
  isLimitCone_functorVertexCone_iff_of_val c _
    ((functorVertexEquiv _ _).symm_apply_apply c.val)

end SerrePositivity.InfinityCategories.F2
