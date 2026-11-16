module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementNondegenerate
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementFaces
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergePurity

/-!
概要：実併合の右残余射が非同型の場合に細分した全単体の非退化性を証明する。
方針：併合で対象の個数が一つ減ることと、元のnerveの隣接退化の排除を合わせる。
規約：右残余射の非同型性の条件は明示し、親の全存在とは区別する。
使われ方：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実残余射が非同型なら非退化な全単体の実併合による細分も非退化。
方針：指定面の実因子化と両隣の退化の排除を適用する。
規約：右残余射の非同型性の条件つきの法則。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionBottomMergeRefinement_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hg : ¬ IsIso (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)) :
    ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2) :=
  composableArrowRefinement_nondegenerate H k _ _ _
    (walkingAdjunctionBottomMerge_factor (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)
    hnd (walkingAdjunctionBottomMergeObject_ne (H.obj k.castSucc) m hA) hg


/-- 概要：一つだけの最初の併合の全点の条件に一致しなければ細分は非退化。
方針：実残余射の同型性の同値を使って両隣の退化を排除する。
規約：有限個数と全点の値の具体的条件。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionBottomMergeRefinement_nondegenerate_of_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp : ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1)) :
    ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2) := by
  apply walkingAdjunctionBottomMergeRefinement_nondegenerate H k m hA h1 hnd
  intro hg
  have := hg
  exact hp (walkingAdjunctionBottomMerge_pure_of_residual_isIso
    (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)

end SerrePositivity.InfinityCategories.HA.Monads
