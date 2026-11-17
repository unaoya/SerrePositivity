module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIsoDegeneracy
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementNondegenerate
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstRefinement

/-!
概要：実併合による細分の非退化性を、一つだけの併合でないという全点条件と同値にする。
方針：新しい単体が非退化なら隣接する実右因子は非同型となることを回収する。
規約：先の十分条件の逆も元のHomの単体集合で証明する。
使われ方：Riehl–Verity §4.1–§4.2の実親の検収、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の厳密な併合と退化の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：細分した実全単体が非退化なら実残余射は非同型。
方針：挿入した右辺を回収し、非退化な全単体の全隣接辺の非同型性を適用する。
規約：実残余射の非同型性を結論として得る。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionBottomMergeResidual_not_isIso_of_nondegenerate
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) :
    ¬ IsIso (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1) := by
  intro hi
  let q := walkingAdjunctionBottomMergeArrow (H.obj k.castSucc) m hA
  let g := walkingAdjunctionBottomMergeResidual (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  let G := walkingAdjunctionBottomMergeRefinement H k m hA h1
  have hno := (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso G).mp hnd k.succ
  apply hno
  have : IsIso g := hi
  have hm : G.obj k.succ.castSucc = walkingAdjunctionBottomMergeObject Y m :=
    composableArrowRefinement_middle n H k _ q g
  have ht : G.obj k.succ.succ = H.obj k.succ := by
    have ho := CategoryTheory.Functor.congr_obj
      (walkingAdjunctionBottomMergeRefinement_face H k m hA h1) k.succ
    change G.obj (k.succ.castSucc.succAbove k.succ) = H.obj k.succ at ho
    rw [Fin.succAbove_castSucc_self] at ho
    exact ho
  exact isIso_of_equal_objects_hom_heq hm.symm ht.symm g _
    (composableArrowRefinement_right_edge n H k _ q g).symm

/-- 概要：元が非退化なら、実細分の非退化性は一つだけの併合でないという全点条件と同値。
方針：非退化な右辺からの非同型性と、実残余射の同型性の全点表示を合わせる。
規約：元の単体集合の非退化性の両方向。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionBottomMergeRefinement_nondegenerate_iff_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1) := by
  constructor
  · intro hnew hp
    have hg := walkingAdjunctionBottomMergeResidual_not_isIso_of_nondegenerate H k m hA h1 hnew
    exact hg (walkingAdjunctionBottomMerge_residual_isIso_of_pure
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1 hp)
  · exact walkingAdjunctionBottomMergeRefinement_nondegenerate_of_not_pure H k m hA h1 hnd

/-- 概要：実際に選んだ最初の細分は、元の最初の辺が一つだけの併合でないときに限り非退化。
方針：実最小元と実併合で構成した全単体に両方向の判定を適用する。
規約：位置や同型性を仮定し直さず具体的な全点条件で述べる。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionFirstRefinement_nondegenerate_iff_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
    let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
    (ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1) :=
  walkingAdjunctionBottomMergeRefinement_nondegenerate_iff_not_pure H _ _ _ _ hnd

end SerrePositivity.InfinityCategories.HA.Monads
