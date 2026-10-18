module
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# 反対圏の nerve の反転した単体

概要：反対圏の可合成射の列を順序と向きを反転した元の圏の列へ送る。
方針：頂点 i を i.rev で評価し、射を unop する。
規約：KST Proposition 4.14、SW92 §1.2 の反対 bar の実比較。
使われ方：反対モノイドの bar と単体の順序反転を同定する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
variable {C : Type u} [Category.{v} C]

/-- 概要：反対圏の可合成射の列の順序と向きを反転する実写像。
方針：rev の反変な順序と unop の合成の逆転を組み合わせる。
規約：SW92 §1.2。使われ方：反対 nerve の単体ごとの実比較。 -/
def oppositeNerveSimplex {n : ℕ} (F : ComposableArrows Cᵒᵖ n) : ComposableArrows C n where
  obj i := unop (F.obj i.rev)
  map {i j} h := (F.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom h)))).unop
  map_id i := by
    rw [show homOfLE (Fin.rev_le_rev.mpr (leOfHom (𝟙 i))) = 𝟙 i.rev from Subsingleton.elim _ _,
      F.map_id]
    rfl
  map_comp f g := by
    rw [← unop_comp, ← F.map_comp]
    congr 1

/-- 概要：元の圏の列を順序と向きを反転して反対圏へ送る実写像。
方針：rev と op を組み合わせる。
規約：SW92 §1.2。使われ方：反対 nerve の実比較の逆写像。 -/
def nerveOppositeSimplex {n : ℕ} (F : ComposableArrows C n) : ComposableArrows Cᵒᵖ n where
  obj i := op (F.obj i.rev)
  map {i j} h := (F.map (homOfLE (Fin.rev_le_rev.mpr (leOfHom h)))).op
  map_id i := by
    rw [show homOfLE (Fin.rev_le_rev.mpr (leOfHom (𝟙 i))) = 𝟙 i.rev from Subsingleton.elim _ _,
      F.map_id]
    rfl
  map_comp f g := by
    rw [← op_comp, ← F.map_comp]
    congr 1

/-- 概要：列の順序と向きの二回の反転は恒等。
方針：rev の involution と op・unop の相殺を使う。
規約：SW92 §1.2。使われ方：反対 nerve の実全単射の片側の逆。 -/
lemma oppositeNerveSimplex_nerveOppositeSimplex {n : ℕ} (F : ComposableArrows C n) :
    oppositeNerveSimplex (nerveOppositeSimplex F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    simp [oppositeNerveSimplex, nerveOppositeSimplex]
  case h_map =>
    intro i j h
    simp only [oppositeNerveSimplex, nerveOppositeSimplex, Quiver.Hom.unop_op, Quiver.Hom.op_unop]
    rw [← eqToHom_map F (Fin.rev_rev i), ← eqToHom_map F (Fin.rev_rev j).symm,
      ← F.map_comp, ← F.map_comp]
    congr 1

/-- 概要：反対圏でも列の二回の反転は恒等。
方針：rev の involution と unop・op の相殺を使う。
規約：SW92 §1.2。使われ方：反対 nerve の実全単射の他側の逆。 -/
lemma nerveOppositeSimplex_oppositeNerveSimplex {n : ℕ} (F : ComposableArrows Cᵒᵖ n) :
    nerveOppositeSimplex (oppositeNerveSimplex F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    simp [oppositeNerveSimplex, nerveOppositeSimplex]
  case h_map =>
    intro i j h
    simp only [oppositeNerveSimplex, nerveOppositeSimplex, Quiver.Hom.unop_op, Quiver.Hom.op_unop]
    rw [← eqToHom_map F (Fin.rev_rev i), ← eqToHom_map F (Fin.rev_rev j).symm,
      ← F.map_comp, ← F.map_comp]
    congr 1

end SerrePositivity.KST.ProExcision
