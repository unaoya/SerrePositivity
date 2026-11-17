module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：元のnerveの退化で重なる辺は同型であり、対象と射の照合に沿って同型性を戻せる。
方針：退化の順序関手で同じ点になる辺を恒等射の輸送として比較する。
規約：任意の実圏の元のnerveの作用を使う。
使われ方：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の退化の排除。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C : Type u} [Category.{v} C]

/-- 概要：同じ対象に沿って照合した射の異種等式は同型性を保つ。
方針：対象を同一視して実射の等式へ戻す。規約：両端の対象の等式も明示する。
使われ方：Riehl–Verity §4.1の実残余射の退化の排除。 -/
lemma isIso_of_equal_objects_hom_heq {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) [IsIso f] : IsIso g := by
  subst A'
  subst B'
  have he : f = g := eq_of_heq h
  subst g
  infer_instance

/-- 概要：元のnerveの退化で二点が重なる辺の像は同型。
方針：順序関手の実辺は同じ点の恒等射の輸送であり、元の関手はそれを保つ。
規約：元のnerveの全射の作用を使う。使われ方：Riehl–Verity §4.1の退化した細分の検出。 -/
lemma nerve_degeneracy_edge_isIso {n : ℕ} (F : ComposableArrows C n) (j : Fin (n + 1)) :
    IsIso (((nerve C).σ j F).map (homOfLE (Fin.castSucc_le_succ j))) := by
  let P := (SimplexCategory.σ j).toOrderHom.monotone.functor
  have hp : P.obj j.castSucc = P.obj j.succ := by
    change j.predAbove j.castSucc = j.predAbove j.succ
    simp
  have : IsIso (P.map (homOfLE (Fin.castSucc_le_succ j))) := by
    have he : P.map (homOfLE (Fin.castSucc_le_succ j)) = eqToHom hp := Subsingleton.elim _ _
    rw [he]
    infer_instance
  change IsIso (F.map (P.map (homOfLE (Fin.castSucc_le_succ j))))
  infer_instance

end SerrePositivity.InfinityCategories.HA.Monads
