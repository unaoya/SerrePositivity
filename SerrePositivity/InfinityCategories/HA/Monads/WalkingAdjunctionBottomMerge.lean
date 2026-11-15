module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalBottomMerge
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixInclusions

/-!
概要：最初の二点の併合による因子化を元のminusからの実Homの射へ戻す。
方針：一つ小さい実対象を作り、端点条件と個数の輸送で二つの実射を回収する。
規約：共通表示だけで終えず、元の全射の合成の等式を証明する。
使われ方：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実単体の細分。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最初の二点を併合した後の元の実Homの対象。
方針：混合Homは一つ小さい単体、自己Homは一つ小さい区間を使う。
規約：始点はminusで終点は保持する。使われ方：Riehl–Verity §4.1の実親の中間対象。 -/
def walkingAdjunctionBottomMergeObject (Y : WalkingAdjunctionPoint) (m : ℕ) :
    walkingAdjunctionHom .minus Y := by
  cases Y
  · exact ⟨⦋m⦌⟩
  · exact op (augmentedOrdinalOfCard m)

/-- 概要：併合後の実対象の点の個数はm+1。
方針：元の二つの表示の個数を計算する。規約：指定の同じ実対象。
使われ方：Riehl–Verity §4.1の併合射の型の移送。 -/
lemma walkingAdjunctionBottomMergeObject_card (Y : WalkingAdjunctionPoint) (m : ℕ) :
    walkingAdjunctionOrdinalCard .minus Y (walkingAdjunctionBottomMergeObject Y m) = m + 1 := by
  cases Y
  · rfl
  · change augmentedOrdinalCard (augmentedOrdinalOfCard m) + 1 = m + 1
    rw [augmentedOrdinalCard_ofCard]

/-- 概要：最初の二点を併合する元の実Homの射。
方針：有限単調射の両端の保存を個数の輸送で移して回収する。
規約：実射の存在を仮定しない。使われ方：Riehl–Verity §4.1の親の最初の併合。 -/
def walkingAdjunctionBottomMergeArrow {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    A ⟶ walkingAdjunctionBottomMergeObject Y m :=
  walkingAdjunctionHomOfOrder _ _
    (ordinalOrderHomTransport hA.symm (walkingAdjunctionBottomMergeObject_card Y m).symm
      (ordinalBottomMerge m))
    (ordinalOrderHomTransport_boundary _ _ .minus Y _
      ⟨(ordinalBottomMerge_boundary m).1, fun _ => (ordinalBottomMerge_boundary m).2 rfl⟩)

/-- 概要：実併合射の共通表示は有限単調射の併合の輸送。
方針：実射の回収の往復を使う。規約：同じ射の全表示。
使われ方：Riehl–Verity §4.1の実因子化の検収。 -/
lemma walkingAdjunctionBottomMergeArrow_profile {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) =
      ordinalOrderHomTransport hA.symm (walkingAdjunctionBottomMergeObject_card Y m).symm
        (ordinalBottomMerge m) := walkingAdjunctionOrderHom_ofOrder _ _ _ _

/-- 概要：二番目の点の像0は個数の輸送後にも成立する。
方針：値1の点で輸送の異種等式を評価する。規約：元の全射の共通表示を使う。
使われ方：Riehl–Verity §4.1の実残余射の最小元の条件。 -/
lemma walkingAdjunctionBottomMerge_raw_one {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    ((ordinalOrderHomTransport hA rfl (walkingAdjunctionOrderHom f))
      (0 : Fin (m + 1)).succ).val = 0 := by
  let i : Fin (walkingAdjunctionOrdinalCard .minus Y A) := ⟨1, by omega⟩
  have he := ordinalOrderHom_heq_val hA rfl (walkingAdjunctionOrderHom f) _
    (ordinalOrderHomTransport_heq hA rfl (walkingAdjunctionOrderHom f)).symm
    i (0 : Fin (m + 1)).succ rfl
  exact he.symm.trans (h1 i rfl)

/-- 概要：併合の後の元の実Homの残余射。
方針：元の全射の共通表示を切断と合成し、最小元・指定の最大元の条件から回収する。
規約：残余射を存在の仮定にしない。使われ方：Riehl–Verity §4.1の実親の残りの射。 -/
def walkingAdjunctionBottomMergeResidual {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionBottomMergeObject Y m ⟶ B :=
  walkingAdjunctionHomOfOrder _ _
    (ordinalOrderHomTransport (walkingAdjunctionBottomMergeObject_card Y m).symm rfl
      ((ordinalOrderHomTransport hA rfl (walkingAdjunctionOrderHom f)).comp
        (ordinalBottomMergeSection m)))
    (ordinalOrderHomTransport_boundary _ _ .minus Y _
      (ordinalBottomMerge_residual_boundary Y _
        (ordinalOrderHomTransport_boundary hA rfl .minus Y _ (walkingAdjunctionOrderHom_boundary f))
        (walkingAdjunctionBottomMerge_raw_one f m hA h1)))

/-- 概要：実残余射の共通表示は元の射と切断の合成の輸送。
方針：実射の回収の往復を使う。規約：全有限単調射の表示。
使われ方：Riehl–Verity §4.1の元の全射の因子化。 -/
lemma walkingAdjunctionBottomMergeResidual_profile {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeResidual f m hA h1) =
      ordinalOrderHomTransport (walkingAdjunctionBottomMergeObject_card Y m).symm rfl
        ((ordinalOrderHomTransport hA rfl (walkingAdjunctionOrderHom f)).comp
          (ordinalBottomMergeSection m)) := walkingAdjunctionOrderHom_ofOrder _ _ _ _

/-- 概要：実併合射と実残余射の合成は元の実射。
方針：共通表示の全合成則、個数の輸送と有限単調射の因子化を合わせる。
規約：元のHomの射の等式で検収する。使われ方：Riehl–Verity §4.1の実親の面の照合。 -/
lemma walkingAdjunctionBottomMerge_factor {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0) :
    walkingAdjunctionBottomMergeArrow A m hA ≫ walkingAdjunctionBottomMergeResidual f m hA h1 =
      f := by
  apply walkingAdjunctionOrderHom_injective
  rw [walkingAdjunctionOrderHom_comp, walkingAdjunctionBottomMergeArrow_profile,
    walkingAdjunctionBottomMergeResidual_profile]
  rw [← ordinalOrderHomTransport_comp hA.symm
    (walkingAdjunctionBottomMergeObject_card Y m).symm rfl]
  let raw := ordinalOrderHomTransport hA rfl (walkingAdjunctionOrderHom f)
  have hb := ordinalOrderHomTransport_boundary hA rfl .minus Y _
    (walkingAdjunctionOrderHom_boundary f)
  have h0 : (raw 0).val = 0 := hb.1 rfl 0 rfl
  have h1' : (raw (0 : Fin (m + 1)).succ).val = 0 :=
    walkingAdjunctionBottomMerge_raw_one f m hA h1
  have he : raw 0 = raw (0 : Fin (m + 1)).succ := Fin.ext (h0.trans h1'.symm)
  rw [ordinalBottomMerge_factor raw he]
  exact eq_of_heq ((ordinalOrderHomTransport_heq hA.symm rfl raw).trans
    (ordinalOrderHomTransport_heq hA rfl (walkingAdjunctionOrderHom f)))

end SerrePositivity.InfinityCategories.HA.Monads
