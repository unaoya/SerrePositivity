module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Hom の宇宙を上げた圏の nerve の実同型

概要：Hom の ULift の nerve と、元の nerve の単体の ULift を実同型で比較する。
方針：同じ合成可能射列に up・down を適用し、全作用素との交換を定義で示す。
規約：元の対象・射列・全単体作用素を保持する。
使われ方：Dwyer–Kan §7 の共通比較の始域の宇宙調整。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom

open CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- 概要：元の Hom の up の後の down は同じ元の関手（Dwyer–Kan §7）。
方針：各射の ULift の順逆を評価する。
規約：元の対象・射・関手の厳密な等式。
使われ方：nerve の実同型の逆則。 -/
lemma up_down : ULiftHom.up.{v, u, w} (C := C) ⋙ ULiftHom.down = 𝟭 C := rfl

/-- 概要：元の Hom の down の後の up も恒等（Dwyer–Kan §7）。
方針：元の射の ULift の eta 則を使う。
規約：同じ ULiftHom の関手の厳密な等式。
使われ方：nerve の実同型の反対側の逆則。 -/
lemma down_up : ULiftHom.down.{v, u, w} (C := C) ⋙ ULiftHom.up = 𝟭 (ULiftHom.{w} C) := rfl

/-- 概要：Hom の ULift の nerve は元の nerve の ULift と実同型（Dwyer–Kan §7）。
方針：元の射列の全射を up・down し、同じ二つの厳密な逆則を使う。
規約：同型の順射は元の射列の down そのもの。
使われ方：共通比較の始域を同じ大きい宇宙で扱う。 -/
def iso : nerve (ULiftHom.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) where
  hom :=
    { app _ := ↾fun c => ULift.up (c ⋙ ULiftHom.down.{v, u, w})
      naturality _ _ _ := rfl }
  inv :=
    { app _ := ↾fun c => c.down ⋙ ULiftHom.up.{v, u, w}
      naturality _ _ _ := rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro c
    change (c ⋙ ULiftHom.down.{v, u, w}) ⋙ ULiftHom.up = c
    rw [Functor.assoc, down_up, Functor.comp_id]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro c
    apply ULift.ext
    change (c.down ⋙ ULiftHom.up.{v, u, w}) ⋙ ULiftHom.down = c.down
    rw [Functor.assoc, up_down, Functor.comp_id]

/-- 概要：同じ nerve の実同型は元の圏の関手にも自然（Dwyer–Kan §7）。
方針：全射列を係数関手で送る二つの順序を比較する。
規約：元の関手の対象・射への作用を保持する。
使われ方：共通比較の係数自然性。 -/
lemma naturality {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    nerveMap (ULiftHom.down.{v, u, w} ⋙ F ⋙ ULiftHom.up) ≫ (iso D).hom =
      (iso C).hom ≫ SSet.uliftFunctor.map (nerveMap F) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NerveULiftHom
