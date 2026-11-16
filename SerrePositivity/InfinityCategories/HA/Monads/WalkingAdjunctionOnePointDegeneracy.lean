module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegeneracies
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints

/-!
概要：全頂点が一点の実全単体は定値で、正の次元では元のnerveで退化する。
方針：個数による対象の一意性と共通表示の忠実性で定値関手を回収する。
規約：非退化性は元のHomの単体集合のものを使う。
使われ方：Riehl–Verity §4.1–§4.2の原子の最初の併合の選択、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全頂点の共通表示が一点なら元の実関手は定値。
方針：重みの単射性と一点への射の一意性を使う。規約：全射を含む実関手の等式。
使われ方：Riehl–Verity §4.1の退化の検出。 -/
lemma walkingAdjunctionConst_of_card_one {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hc : ∀ i, walkingAdjunctionOrdinalCard X Y (H.obj i) = 1) :
    H = (Functor.const _).obj (H.obj 0) := by
  have ho (i : Fin (n + 1)) : H.obj i = H.obj 0 := by
    apply walkingAdjunctionWeight_injective X Y
    have hi := walkingAdjunctionOrdinalCard_weight X Y (H.obj i)
    have h0 := walkingAdjunctionOrdinalCard_weight X Y (H.obj 0)
    have hci := hc i
    have hc0 := hc 0
    omega
  have hh (i j : Fin (n + 1)) : Subsingleton (H.obj i ⟶ H.obj j) := by
    refine ⟨fun f g => ?_⟩
    apply walkingAdjunctionOrderHom_injective
    apply OrderHom.ext
    funext k
    apply Fin.ext
    have hf := (walkingAdjunctionOrderHom f k).isLt
    have hg := (walkingAdjunctionOrderHom g k).isLt
    have hcj := hc j
    omega
  refine CategoryTheory.Functor.ext ho ?_
  intro i j f
  exact @Subsingleton.elim _ (hh i j) _ _

/-- 概要：正の次元で全頂点が一点の全単体は元のnerveで退化する。
方針：一点の定値な一つ低次の全単体を実退化で送る。
規約：元のHomの単体集合の退化の像として与える。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionHomShape_degenerate_of_card_one {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom X Y)
    (hc : ∀ i, walkingAdjunctionOrdinalCard X Y (H.obj i) = 1) :
    ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).degenerate (n + 1) := by
  let T : Fin (n + 1) ⥤ walkingAdjunctionHom X Y := (Functor.const _).obj (H.obj 0)
  have hconst := walkingAdjunctionConst_of_card_one H hc
  have he : (WalkingAdjunctionHomShape.{u} X Y).σ (0 : Fin (n + 1)) (ULift.up T) =
      ULift.up H := by
    apply ULift.ext
    change (walkingAdjunctionSimplexFunctor (SimplexCategory.σ (0 : Fin (n + 1))) ⋙ T) = H
    exact hconst.symm
  have hd := (WalkingAdjunctionHomShape.{u} X Y).σ_mem_degenerate
    (0 : Fin (n + 1)) (ULift.up T)
  exact he ▸ hd

/-- 概要：minusからの正の次元の非退化な全単体には二点以上の頂点がある。
方針：全頂点が一点なら元のnerveの退化となることに反する。
規約：元の単体集合の非退化性を使う。使われ方：Riehl–Verity §4.1の最初の併合の選択。 -/
lemma walkingAdjunctionHomShape_exists_large_vertex {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (h : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ∃ i, 2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj i) := by
  by_contra hn
  have hc (i : Fin (n + 2)) : walkingAdjunctionOrdinalCard .minus Y (H.obj i) = 1 := by
    have hp := NeZero.pos (walkingAdjunctionOrdinalCard .minus Y (H.obj i))
    have hi : ¬ 2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj i) := by
      intro hi
      exact hn ⟨i, hi⟩
    omega
  exact (SSet.mem_nonDegenerate_iff_notMem_degenerate _ _).mp h
    (walkingAdjunctionHomShape_degenerate_of_card_one H hc)

end SerrePositivity.InfinityCategories.HA.Monads
