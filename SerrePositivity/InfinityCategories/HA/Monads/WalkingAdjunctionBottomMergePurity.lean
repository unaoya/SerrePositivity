module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIsomorphismProfiles
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeLaws

/-!
概要：実併合の残余射の同型性を、一つだけの最初の併合という全点の条件へ照合する。
方針：同型の実順序表示と、実因子化の等式・右因子の一意性を使う。
規約：元のHom内の同型性と有限個数・全点の値の両方向を証明する。
使われ方：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の厳密な併合の表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実併合射の値は元の点の値から1を引いたもの。
方針：共通表示の輸送の異種等式を同じ値の実点で評価する。
規約：先頭0は0にとどまる。使われ方：Riehl–Verity §4.1の一つの併合の全点の表示。 -/
lemma walkingAdjunctionBottomMergeArrow_val {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (i : Fin (walkingAdjunctionOrdinalCard .minus Y A)) :
    (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) i).val = i.val - 1 := by
  have he : HEq (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA))
      (ordinalBottomMerge m) :=
    (heq_of_eq (walkingAdjunctionBottomMergeArrow_profile A m hA)).trans
      (ordinalOrderHomTransport_heq _ _ _)
  exact ordinalOrderHom_heq_val hA (walkingAdjunctionBottomMergeObject_card Y m) _ _ he
    i ((Fin.castOrderIso hA) i) rfl

/-- 概要：残余射が同型なら元の射は一つだけの最初の併合。
方針：実同型の個数・値の保存と元の実因子化を合わせる。
規約：終点の個数と全点の値の条件を結論にする。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionBottomMerge_pure_of_residual_isIso {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    [IsIso (walkingAdjunctionBottomMergeResidual f m hA h1)] :
    walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1 := by
  let q := walkingAdjunctionBottomMergeArrow A m hA
  let g := walkingAdjunctionBottomMergeResidual f m hA h1
  have hc := walkingAdjunctionCard_eq_of_isIso g
  have hobj := walkingAdjunctionBottomMergeObject_card Y m
  refine ⟨by omega, ?_⟩
  intro i
  have he := congrArg (fun h => walkingAdjunctionOrderHom h)
    (walkingAdjunctionBottomMerge_factor f m hA h1)
  rw [walkingAdjunctionOrderHom_comp] at he
  have hi := congrArg (fun h => (h i).val) he
  change (walkingAdjunctionOrderHom g (walkingAdjunctionOrderHom q i)).val =
    (walkingAdjunctionOrderHom f i).val at hi
  have hg := walkingAdjunctionOrderHom_val_of_isIso g (walkingAdjunctionOrderHom q i)
  have hq : (walkingAdjunctionOrderHom q i).val = i.val - 1 :=
    walkingAdjunctionBottomMergeArrow_val A m hA i
  omega

/-- 概要：元の射が一つだけの最初の併合なら実残余射は同型。
方針：終点を実併合後の対象と同一視し、全点の値で因子化を比較して一意性を使う。
規約：元のHom内の同型性を結論にする。使われ方：Riehl–Verity §4.1の厳密な併合の照合。 -/
lemma walkingAdjunctionBottomMerge_residual_isIso_of_pure {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    (hp : walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
        (walkingAdjunctionOrderHom f i).val = i.val - 1) :
    IsIso (walkingAdjunctionBottomMergeResidual f m hA h1) := by
  have hB : walkingAdjunctionBottomMergeObject Y m = B := by
    apply walkingAdjunctionWeight_injective .minus Y
    have hm := walkingAdjunctionOrdinalCard_weight .minus Y (walkingAdjunctionBottomMergeObject Y m)
    have hb := walkingAdjunctionOrdinalCard_weight .minus Y B
    have hc := walkingAdjunctionBottomMergeObject_card Y m
    have ht := hp.1
    omega
  let r := eqToHom hB
  have hf : walkingAdjunctionBottomMergeArrow A m hA ≫ r = f := by
    apply walkingAdjunctionOrderHom_injective
    apply OrderHom.ext
    funext i
    apply Fin.ext
    rw [walkingAdjunctionOrderHom_comp]
    exact (walkingAdjunctionOrderHom_val_of_isIso r _).trans
      ((walkingAdjunctionBottomMergeArrow_val A m hA i).trans (hp.2 i).symm)
  have he := walkingAdjunctionBottomMergeResidual_unique f m hA h1 r hf
  rw [← he]
  change IsIso (eqToHom hB)
  infer_instance

/-- 概要：残余射の同型性と一つだけの最初の併合という全点の条件は同値。
方針：構成した実同型と全点の表示の両方向を合わせる。
規約：元の射と構成した実残余射を使う。使われ方：Riehl–Verity §4.1の実親の条件。 -/
lemma walkingAdjunctionBottomMerge_residual_isIso_iff_pure {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    IsIso (walkingAdjunctionBottomMergeResidual f m hA h1) ↔
      walkingAdjunctionOrdinalCard .minus Y B = m + 1 ∧
        ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
          (walkingAdjunctionOrderHom f i).val = i.val - 1 := by
  constructor
  · intro h
    have := h
    exact walkingAdjunctionBottomMerge_pure_of_residual_isIso f m hA h1
  · exact walkingAdjunctionBottomMerge_residual_isIso_of_pure f m hA h1

end SerrePositivity.InfinityCategories.HA.Monads
