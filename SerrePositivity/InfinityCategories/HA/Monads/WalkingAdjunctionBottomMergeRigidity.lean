module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowEpiFaceRigidity
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementFirstMerge

/-!
概要：一つだけの実併合の全点条件と指定面は実細分の全関手を一意に定める。
方針：全点条件から中間対象・左辺・epiを回収し、指定面内の合成で右辺を定める。
規約：親の実全関手の等式を結論にする。
使われ方：Riehl–Verity §4.1–§4.2の実親の一意性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の厳密な細分の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：同じ始点を持ち同じ純粋な併合条件を満たす二辺は、終点も実射も一致する。
方針：終点の個数の剛性と全点の値の忠実性を使う。
規約：元の四Hom内の実等式。使われ方：Riehl–Verity §4.1の挿入左辺の一意性。 -/
lemma walkingAdjunctionPureBottomMerge_rigidity {Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom .minus Y} (hA : A = A')
    (f : A ⟶ B) (g : A' ⟶ B') (m : ℕ)
    (hf : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1)
    (hg : walkingAdjunctionOrdinalCard .minus Y B' = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A'),
        (walkingAdjunctionOrderHom g i).val = i.val - 1) :
    B = B' ∧ HEq f g := by
  have hB : B = B' := by
    apply walkingAdjunctionWeight_injective .minus Y
    have hb := walkingAdjunctionOrdinalCard_weight .minus Y B
    have hb' := walkingAdjunctionOrdinalCard_weight .minus Y B'
    have hc := hf.1.trans hg.1.symm
    omega
  refine ⟨hB, ?_⟩
  subst A'
  subst B'
  apply heq_of_eq
  apply walkingAdjunctionOrderHom_injective
  apply OrderHom.ext
  funext i
  apply Fin.ext
  exact (hf.2 i).trans (hg.2 i).symm

/-- 概要：構成した実併合射は元のHomでepi。
方針：全射性から既に証明した右因子の消去則を使う。
規約：epiを仮定せず構成する。使われ方：Riehl–Verity §4.1の右辺の一意性。 -/
lemma walkingAdjunctionBottomMergeArrow_epi {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    Epi (walkingAdjunctionBottomMergeArrow A m hA) := by
  constructor
  intro B f g h
  exact walkingAdjunctionBottomMergeArrow_cancel A m hA f g h

/-- 概要：一つだけの併合の全点条件を満たす元の実辺もepi。
方針：構成した併合射と両端・全射を同一視する。
規約：epiの証人は全点条件から構成。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionPureBottomMerge_epi {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (hp : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) : Epi f := by
  have h := walkingAdjunctionPureBottomMerge_rigidity rfl f
    (walkingAdjunctionBottomMergeArrow A m hA) m hp
    ⟨walkingAdjunctionBottomMergeObject_card Y m, walkingAdjunctionBottomMergeArrow_val A m hA⟩
  obtain ⟨hB, he⟩ := h
  cases hB
  have hf : f = walkingAdjunctionBottomMergeArrow A m hA := eq_of_heq he
  rw [hf]
  exact walkingAdjunctionBottomMergeArrow_epi A m hA

/-- 概要：指定面と一つだけの併合の全点条件を持つ実親は構成済みの細分に一致する。
方針：面から始点を回収し、全点条件で中間対象・左辺・epiを定め、全鎖の一意性を使う。
規約：候補の存在や右辺の一致を仮定しない。使われ方：Riehl–Verity §4.1の実親の一意性。 -/
lemma walkingAdjunctionBottomMergeRefinement_unique {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (hface : finiteChainFace P k.succ.castSucc = H)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    P = walkingAdjunctionBottomMergeRefinement H k m hA h1 := by
  let G := walkingAdjunctionBottomMergeRefinement H k m hA h1
  have he : finiteChainFace P k.succ.castSucc = finiteChainFace G k.succ.castSucc :=
    hface.trans (walkingAdjunctionBottomMergeRefinement_face H k m hA h1).symm
  have hne : k.castSucc.castSucc ≠ k.succ.castSucc := by
    intro h
    have hv := congrArg (fun t : Fin (n + 3) => t.val) h
    change k.val = k.val + 1 at hv
    omega
  have hs := finiteChainFace_obj_eq _ he _ hne
  have hpair := walkingAdjunctionPureBottomMerge_rigidity hs
    (P.map (homOfLE (Fin.castSucc_le_succ k.castSucc)))
    (G.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) m hp
    (walkingAdjunctionBottomMergeRefinement_pure H k m hA h1)
  have hsrc : P.obj k.castSucc.castSucc = H.obj k.castSucc := by
    have ho := CategoryTheory.Functor.congr_obj hface k.castSucc
    change P.obj (k.succ.castSucc.succAbove k.castSucc) = H.obj k.castSucc at ho
    rw [Fin.succAbove_of_castSucc_lt _ _ (by
      change k.val < k.val + 1
      omega)] at ho
    exact ho
  have hpc : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) = m + 2 :=
    (congrArg (walkingAdjunctionOrdinalCard .minus Y) hsrc).trans hA
  have := walkingAdjunctionPureBottomMerge_epi
    (P.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) m hpc hp
  exact composableArrow_eq_of_face_and_epi_left k he hpair.1 hpair.2

end SerrePositivity.InfinityCategories.HA.Monads
