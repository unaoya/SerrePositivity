module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPreviousFaceParent
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFaceWidthGap

/-!
概要：最初の純粋な実併合の直前の面を、幅の欠損2と深さが減る実親へ分ける。
方針：先行辺の実像が値1を欠くか通るかを、0の保存と非併合から実際に判定する。
規約：新しい面や親の証人を入力に追加しない。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の面の二つの場合、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実順序づけ。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：0を保ち底を併合しない実単調射は、値1を像に持たないか、二番目を二番目に送る。
方針：像に値1があればその原像の下の二番目の点を取り、単調性と非併合で像1を得る。
規約：二番目の点がない場合も含む。使われ方：Riehl–Verity §4.2の実像による場合分け。 -/
lemma ordinalNoOneImage_or_through_one {a b : ℕ} (f : Fin a →o Fin b)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hf : ∀ i, i.val = 1 → (f i).val ≠ 0) :
    (∀ i, (f i).val ≠ 1) ∨ ∃ i, i.val = 1 ∧ (f i).val = 1 := by
  classical
  by_cases h : ∃ i, (f i).val = 1
  · obtain ⟨j, hj⟩ := h
    have hj0 : j.val ≠ 0 := by
      intro hz
      have h := h0 j hz
      omega
    let i : Fin a := ⟨1, by have h := j.isLt; omega⟩
    have hi := hf i rfl
    have hm := f.monotone (show i ≤ j from by change 1 ≤ j.val; omega)
    change (f i).val ≤ (f j).val at hm
    exact Or.inr ⟨i, rfl, by omega⟩
  · exact Or.inl (fun i hi => h ⟨i, hi⟩)

/-- 概要：最初の純粋な実併合の直前の面は、幅が2減るか、幅が元以下で深さが減る実親を持つ。
方針：元の最小性で先行辺の非併合を回収し、実像の二つの場合に検証済みの法則を使う。
規約：前の全点の条件を仮定せず、元の実最初の位置から導く。使われ方：Riehl–Verity §4.2。 -/
lemma walkingAdjunctionPreviousFace_dichotomy {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1) :
    let F := finiteChainFace H k.succ.castSucc
    let fa := walkingAdjunctionInnerFace_atomic H k ha
    (walkingAdjunctionOrdinalWidth F + 2 = walkingAdjunctionOrdinalWidth H) ∨
      ∃ hf : ULift.up F ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1),
        ∃ hp : ULift.up (walkingAdjunctionFirstRefinement F fa hf) ∈
            (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2),
          walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement F fa hf) ≤
            walkingAdjunctionOrdinalWidth H ∧
          (walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement F fa hf)
            (walkingAdjunctionAtomic_endpoint_cards _
              (walkingAdjunctionFirstRefinement_atomic F fa hf)).2 hp).val <
            (walkingAdjunctionFirstBottomMergeIndex H
              (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).val := by
  let f := H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))
  have hf : ∀ i, i.val = 1 → (walkingAdjunctionOrderHom f i).val ≠ 0 := by
    intro i hi hz
    have ho := walkingAdjunctionFirstBottomMergeIndex_minimal H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
      (show WalkingAdjunctionBottomMergeAt H k.castSucc from ⟨i, hi, hz⟩)
    rw [hidx] at ho
    change k.val + 1 ≤ k.val at ho
    omega
  rcases ordinalNoOneImage_or_through_one (walkingAdjunctionOrderHom f)
    (walkingAdjunctionOrderHom_bottom f) hf with hm | ht
  · exact Or.inl (walkingAdjunctionOrdinalWidth_inner_gap_two H k hbc hm hg)
  · exact Or.inr (walkingAdjunctionPreviousFace_parent_control H k ha hnd hidx hbc hg ht)

end SerrePositivity.InfinityCategories.HA.Monads
