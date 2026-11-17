module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalBottomMergeVariation
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthInnerFace

/-!
概要：実併合の直前の辺の像が値1を欠く場合、対応する内側面の幅は2減る。
方針：純粋な底併合と先行辺の変化量を計算し、実幅の欠損の等式へ移す。
規約：元の二つの実射の全点の値と実個数の条件から結論を得る。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の実面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のfiltrationの幅の減少。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：0を保ち二番目の像が1より大きい実単調射の像は、値1を欠く。
方針：0の点と正の点に分け、後者には二番目の点からの単調性を使う。
規約：二番目の点がない場合も含む。使われ方：Riehl–Verity §4.2の幅の欠損の実条件。 -/
lemma ordinalNoOneImage_of_bottom_and_gt_one {a b : ℕ} (f : Fin a →o Fin b)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (h1 : ∀ i, i.val = 1 → 1 < (f i).val) : ∀ i, (f i).val ≠ 1 := by
  intro i hi
  by_cases hz : i.val = 0
  · have h := h0 i hz
    omega
  · let j : Fin a := ⟨1, by have h := i.isLt; omega⟩
    have hj := h1 j rfl
    have hm := f.monotone (show j ≤ i from by change 1 ≤ i.val; omega)
    change (f j).val ≤ (f i).val at hm
    omega

/-- 概要：先行辺の像が値1を欠く純粋な併合の内側面では、実幅はちょうど2減る。
方針：実併合の変化量1と実合成での減少1を、実幅の欠損の等式へ入れる。
規約：原子性・非退化性を要求しない。使われ方：Riehl–Verity §4.2の幅による実順序。 -/
lemma walkingAdjunctionOrdinalWidth_inner_gap_two {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 2)) (k : Fin (n + 1))
    (hcard : walkingAdjunctionOrdinalCard X Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard X Y (H.obj k.succ.castSucc))
    (hmiss : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val ≠ 1)
    (hpure : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1) :
    walkingAdjunctionOrdinalWidth (finiteChainFace H k.succ.castSucc) + 2 =
      walkingAdjunctionOrdinalWidth H := by
  have hg := ordinalMapVariation_bottomMerge _ hcard hpure
  have hf := ordinalMapVariation_comp_bottomMerge_of_no_one _ _ hcard hmiss hpure
  rw [← walkingAdjunctionOrderHom_comp] at hf
  have hw := walkingAdjunctionOrdinalWidth_inner_defect n H k
  omega

end SerrePositivity.InfinityCategories.HA.Monads
