module
public import SerrePositivity.KST.SConstruction.ResolutionNerveMap
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # 離散圏の nerve と定値単体集合の厳密な同型
概要：離散圏の射列をその最初の値で評価し、定値射列を逆にする。
方針：離散圏の射が両端の等号を与えることを使う。
規約：宇宙を変えずに元の離散圏を使う。使われ方：fiber 解消の augmentation の値域。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 概要：離散圏の nerve は同じ集合の定値単体集合と自然に同型。
方針：射列の最初の値と定値な射列を互いに逆にする。
規約：型の同定を局所化に持ち越さない。使われ方：augmentation の各行の弱同値。 -/
def discreteNerveConstantIso (A : Type u) :
    nerve (Discrete A) ≅ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj A where
  hom :=
    { app n := ↾fun c => (c.obj 0).as
      naturality {n l} σ := by
        apply ConcreteCategory.hom_ext
        intro c
        change (c.obj (σ.unop.toOrderHom 0)).as = (c.obj 0).as
        exact (Discrete.eq_of_hom (c.map (homOfLE (Fin.zero_le (σ.unop.toOrderHom 0))))).symm }
  inv :=
    { app n := ↾fun a => (CategoryTheory.Functor.const (Fin (n.unop.len + 1))).obj (Discrete.mk a)
      naturality {_ _} _ := rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    apply nerve.ext_of_isThin
    funext i
    apply Discrete.ext
    exact Discrete.eq_of_hom (c.map (homOfLE (Fin.zero_le i)))
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl

end SerrePositivity.KST.SConstruction
