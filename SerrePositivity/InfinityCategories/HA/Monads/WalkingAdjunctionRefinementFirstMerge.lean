module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementPrefix
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeTransport
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstRefinement
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementNondegenerate

/-!
概要：実併合による細分で最初の併合位置を保ち、その辺の厳密な全点条件を証明する。
方針：前の実辺と挿入した左因子の回収を、併合の実点と最小性へ移す。
規約：位置の実選択と実全鎖の構成を使い、保存を仮定にしない。
使われ方：Riehl–Verity §4.1–§4.2の実親の最初の折り返し、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のfillable条件の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：細分の挿入位置の左辺で二番目の実点は0へ送られる。
方針：左の実射を回収し、実併合射の値を使う。規約：実位置の条件を結論にする。
使われ方：Riehl–Verity §4.1の最初の併合の保存。 -/
lemma walkingAdjunctionBottomMergeRefinement_at {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1)
      k.castSucc := by
  let q := walkingAdjunctionBottomMergeArrow (H.obj k.castSucc) m hA
  let g := walkingAdjunctionBottomMergeResidual (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  let G := walkingAdjunctionBottomMergeRefinement H k m hA h1
  have fac := walkingAdjunctionBottomMerge_factor (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  have hs : G.obj k.castSucc.castSucc = H.obj k.castSucc :=
    composableArrowRefinement_before_obj H k _ q g fac k.castSucc
      (by change k.val ≤ k.val; exact le_rfl)
  have ht : G.obj k.castSucc.succ = walkingAdjunctionBottomMergeObject Y m :=
    composableArrowRefinement_middle n H k _ q g
  apply (walkingAdjunctionMergesBottom_heq hs ht _ q
    (composableArrowRefinement_left_edge n H k _ q g)).mpr
  refine ⟨⟨1, by omega⟩, rfl, ?_⟩
  exact walkingAdjunctionBottomMergeArrow_val (H.obj k.castSucc) m hA _

/-- 概要：細分の挿入位置の左辺は一つだけの最初の併合の全点条件を満たす。
方針：挿入した左因子の実表示と中間対象の実個数を移す。
規約：終点の個数と全点の値を結論にする。使われ方：Riehl–Verity §4.1の厳密な併合。 -/
lemma walkingAdjunctionBottomMergeRefinement_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionBottomMergeRefinement H k m hA h1).obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionBottomMergeRefinement H k m hA h1).obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionBottomMergeRefinement H k m hA h1).map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1 := by
  let q := walkingAdjunctionBottomMergeArrow (H.obj k.castSucc) m hA
  let g := walkingAdjunctionBottomMergeResidual (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  let G := walkingAdjunctionBottomMergeRefinement H k m hA h1
  have fac := walkingAdjunctionBottomMerge_factor (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  have hs : G.obj k.castSucc.castSucc = H.obj k.castSucc :=
    composableArrowRefinement_before_obj H k _ q g fac k.castSucc
      (by change k.val ≤ k.val; exact le_rfl)
  have ht : G.obj k.castSucc.succ = walkingAdjunctionBottomMergeObject Y m :=
    composableArrowRefinement_middle n H k _ q g
  apply (walkingAdjunctionPureBottomMerge_heq hs ht _ q
    (composableArrowRefinement_left_edge n H k _ q g) m).mpr
  exact ⟨walkingAdjunctionBottomMergeObject_card Y m,
    walkingAdjunctionBottomMergeArrow_val (H.obj k.castSucc) m hA⟩

/-- 概要：細分の位置より前の辺の併合条件は元と同じ。
方針：前の実対象と実辺の等式を実点の条件に移す。規約：併合条件の両方向。
使われ方：Riehl–Verity §4.1の最初の位置の検収。 -/
lemma walkingAdjunctionBottomMergeRefinement_before_merge_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    {j : Fin (n + 1)} (hj : j < k) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1)
      j.castSucc ↔ WalkingAdjunctionBottomMergeAt H j := by
  let q := walkingAdjunctionBottomMergeArrow (H.obj k.castSucc) m hA
  let g := walkingAdjunctionBottomMergeResidual (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  have fac := walkingAdjunctionBottomMerge_factor (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1
  exact walkingAdjunctionMergesBottom_heq
    (composableArrowRefinement_before_obj H k _ q g fac j.castSucc (by
      change j.val ≤ k.val
      exact le_of_lt hj))
    (composableArrowRefinement_before_obj H k _ q g fac j.succ (by
      change j.val + 1 ≤ k.val
      exact Nat.succ_le_of_lt hj)) _ _
    (composableArrowRefinement_before_edge n H k _ q g j hj)

/-- 概要：元の最初の位置より前には細分後にも併合の辺はない。
方針：前の実辺の併合条件を戻して元の最小性と比較する。
規約：新しい全鎖の全ての前の位置を含む。使われ方：Riehl–Verity §4.1の最小性の保存。 -/
lemma walkingAdjunctionBottomMergeRefinement_no_earlier_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hmin : ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j)
    {r : Fin (n + 2)} (hr : r < k.castSucc) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1) r := by
  intro h
  let j : Fin (n + 1) := ⟨r.val, by
    have hk := k.isLt
    change r.val < k.val at hr
    omega⟩
  have he : r = j.castSucc := Fin.ext rfl
  have hj : j < k := by
    change r.val < k.val
    change r.val < k.val at hr
    exact hr
  have hnew : WalkingAdjunctionBottomMergeAt
      (walkingAdjunctionBottomMergeRefinement H k m hA h1) j.castSucc := he ▸ h
  have hold := (walkingAdjunctionBottomMergeRefinement_before_merge_iff H k m hA h1 hj).mp hnew
  exact (not_le_of_gt hj) (hmin j hold)

/-- 概要：元の最初の併合の位置は細分後にも最初の位置。
方針：それより前の辺が併合でないことから全ての位置と比較する。
規約：全辺についての最小性を結論にする。使われ方：Riehl–Verity §4.1の実親の位置。 -/
lemma walkingAdjunctionBottomMergeRefinement_minimal {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hmin : ∀ j, WalkingAdjunctionBottomMergeAt H j → k ≤ j) :
    ∀ r, WalkingAdjunctionBottomMergeAt (walkingAdjunctionBottomMergeRefinement H k m hA h1) r →
      k.castSucc ≤ r := by
  intro r hr
  by_contra hn
  exact walkingAdjunctionBottomMergeRefinement_no_earlier_merge H k m hA h1 hmin
    (lt_of_not_ge hn) hr

/-- 概要：実際に選んだ最初の位置は構成した実全単体でも最小の併合位置。
方針：元の有限最小元の所属・最小性に細分の保存則を適用する。
規約：最小性の証人を入力に加えない。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma walkingAdjunctionFirstRefinement_first_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionFirstRefinement H ha hnd) k.castSucc ∧
      ∀ r, WalkingAdjunctionBottomMergeAt (walkingAdjunctionFirstRefinement H ha hnd) r →
        k.castSucc ≤ r := by
  dsimp only
  exact ⟨walkingAdjunctionBottomMergeRefinement_at H _ _ _ _,
    walkingAdjunctionBottomMergeRefinement_minimal H _ _ _ _
      (fun j hj => walkingAdjunctionFirstBottomMergeIndex_minimal H _ hnd hj)⟩

/-- 概要：実際に選んだ実細分の最初の辺は一つだけの併合の全点条件を持つ。
方針：実最小元で構成した実併合射の保存則を使う。
規約：具体的な有限個数と全点の値を結論にする。使われ方：Riehl–Verity §4.1の実親。 -/
lemma walkingAdjunctionFirstRefinement_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    let k := walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
    let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
    walkingAdjunctionOrdinalCard .minus Y ((walkingAdjunctionFirstRefinement H ha hnd).obj
      k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionFirstRefinement H ha hnd).obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionFirstRefinement H ha hnd).map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1 :=
  walkingAdjunctionBottomMergeRefinement_pure H _ _ _ _

/-- 概要：選んだ元の辺が一つだけの併合でなければ構成した実全単体は非退化。
方針：実選択した位置へ全点の条件による非退化性の法則を適用する。
規約：位置と同型性の仮定は加えず具体的な有限条件を使う。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure
    {n : ℕ} {Y : WalkingAdjunctionPoint} (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp :
      let k := walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
      let m := walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2
      ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
        ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
          (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
            i.val - 1)) :
    ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2) :=
  walkingAdjunctionBottomMergeRefinement_nondegenerate_of_not_pure H _ _ _ _ hnd hp

end SerrePositivity.InfinityCategories.HA.Monads
