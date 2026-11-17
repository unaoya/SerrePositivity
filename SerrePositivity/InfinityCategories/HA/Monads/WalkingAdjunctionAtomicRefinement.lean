module

public import Mathlib.Data.Fin.SuccPred
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinement
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeLaws

/-!
概要：実射の細分を全随伴の実全単体へ挿入し、その原子性を証明する。
方針：有限鎖の実再帰と原子性の有限端点による判定を合わせる。
規約：全単体の存在やその原子性を仮定せず、元の全Homの実関手を作る。
使われ方：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の全次元への挿入。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：原子的な実全単体の一辺への細分の挿入は原子性を保つ。
方針：細分した実関手の両端の対象の等式を有限端点の判定へ移す。
規約：全射と実分解を含む元の原子性を結論にする。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionRefinement_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) (k : Fin (n + 1))
    (B : walkingAdjunctionHom X Y) (q : H.obj k.castSucc ⟶ B) (g : B ⟶ H.obj k.succ)
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (composableArrowRefinement H k B q g) := by
  have hc := walkingAdjunctionAtomic_endpoint_cards H h
  apply walkingAdjunctionAtomic_of_endpoint_cards
  · exact (congrArg (walkingAdjunctionOrdinalCard X Y)
      (composableArrowRefinement_first H k B q g)).trans hc.1
  · exact (congrArg (walkingAdjunctionOrdinalCard X Y)
      (composableArrowRefinement_last H k B q g)).trans hc.2

/-- 概要：指定した辺を最初の併合で細分して一つ高次の実全単体を作る。
方針：元の実併合・実残余射を有限鎖の実構成に挿入する。
規約：中間対象と全射は構成済みのものを使う。使われ方：Riehl–Verity §4.1の実親の候補。 -/
def walkingAdjunctionBottomMergeRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2) :=
  composableArrowRefinement H k (walkingAdjunctionBottomMergeObject Y m)
    (walkingAdjunctionBottomMergeArrow (H.obj k.castSucc) m hA)
    (walkingAdjunctionBottomMergeResidual
      (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)

/-- 概要：最初の併合で細分した実全単体は元が原子的なら原子的。
方針：実鎖の両端の保存と有限端点の判定を適用する。
規約：原子性を親の存在の仮定として追加しない。使われ方：Riehl–Verity §4.1の原子の実細分。 -/
lemma walkingAdjunctionBottomMergeRefinement_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionBottomMergeRefinement H k m hA h1) :=
  walkingAdjunctionRefinement_atomic H k _ _ _ h

end SerrePositivity.InfinityCategories.HA.Monads
