module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergePositions
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergePurity

/-!
概要：併合の実点の条件と一つだけの併合の全点条件を、実射の異種等式に沿って移す。
方針：両端の対象を同一視して実射の等式へ戻す。
規約：両端の対象の等式を明示して有限点の型も移す。
使われ方：Riehl–Verity §4.1–§4.2の最初の併合の保存、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の検収。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：両端の対象と実射の照合は二番目の点の像0の条件を保つ。
方針：対象を同一視し同じ有限点へ戻す。規約：実点の存在の条件の両方向。
使われ方：Riehl–Verity §4.1の最初の併合の位置の保存。 -/
lemma walkingAdjunctionMergesBottom_heq {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    (∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y A), i.val = 1 ∧
      (walkingAdjunctionOrderHom f i).val = 0) ↔
    (∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'), i.val = 1 ∧
      (walkingAdjunctionOrderHom g i).val = 0) := by
  subst A'
  subst B'
  have he : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：両端の対象と実射の照合は一つだけの併合の全点条件を保つ。
方針：対象を同一視して個数と点の値を比較する。規約：具体的条件の両方向。
使われ方：Riehl–Verity §4.1の厳密な最初の併合の保存。 -/
lemma walkingAdjunctionPureBottomMerge_heq {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) (m : ℕ) :
    (walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y B' = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'),
        (walkingAdjunctionOrderHom g i).val = i.val - 1) := by
  subst A'
  subst B'
  have he : f = g := eq_of_heq h
  subst g
  rfl

end SerrePositivity.InfinityCategories.HA.Monads
