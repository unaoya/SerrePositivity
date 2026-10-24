module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OppositeSimplex

/-!
概要：反対圏の射列と元の圏の逆順の射列の間の全単射。
方針：射列の順序と矢印を反転し二重反転を消去する。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の局所添字の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
namespace SerrePositivity.InfinityCategories.F1B

variable {C : Type u} [Category.{u} C]

/-- 概要：列の順序と向きの二回の反転は恒等。
方針：rev の involution と op・unop の相殺を使う。
規約：通常の圏の反対圏と単体の反転を区別する。
使われ方：反対 nerve の実全単射の片側の逆。 -/
lemma oppositeNerveSimplex_nerveOppositeSimplex {n : ℕ} (F : ComposableArrows C n) :
    SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex (SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    simp [SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex, SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex]
  case h_map =>
    intro i j h
    simp only [SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex, SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex,
      Quiver.Hom.unop_op]
    rw [← eqToHom_map F (Fin.rev_rev i), ← eqToHom_map F (Fin.rev_rev j).symm,
      ← F.map_comp, ← F.map_comp]
    congr 1

/-- 概要：反対圏でも列の二回の反転は恒等。
方針：rev の involution と unop・op の相殺を使う。
規約：通常の圏の反対圏と単体の反転を区別する。
使われ方：反対 nerve の実全単射の他側の逆。 -/
lemma nerveOppositeSimplex_oppositeNerveSimplex {n : ℕ} (F : ComposableArrows Cᵒᵖ n) :
    SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex (SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex F) = F := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    simp [SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex, SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex]
  case h_map =>
    intro i j h
    simp only [SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex, SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex,
      Quiver.Hom.op_unop]
    rw [← eqToHom_map F (Fin.rev_rev i), ← eqToHom_map F (Fin.rev_rev j).symm,
      ← F.map_comp, ← F.map_comp]
    congr 1

/-- 概要：反対圏の列と元の圏の列の反転による実全単射。
方針：二回の反転が恒等となる二つの実写像を使う。
規約：通常の圏の反対圏と単体の反転を区別する。
使われ方：反対 nerve の各次数の実同型。 -/
def oppositeNerveSimplexEquiv (C : Type u) [Category.{u} C] (n : ℕ) :
    ComposableArrows Cᵒᵖ n ≃ ComposableArrows C n where
  toFun := SerrePositivity.InfinityCategories.F1B.oppositeNerveSimplex
  invFun := SerrePositivity.InfinityCategories.F1B.nerveOppositeSimplex
  left_inv := nerveOppositeSimplex_oppositeNerveSimplex
  right_inv := oppositeNerveSimplex_nerveOppositeSimplex

end SerrePositivity.InfinityCategories.F1B
