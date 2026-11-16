module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFaceMergeEdges
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidth

/-!
概要：先行辺が底の二点を併合せず、底併合との合成が純粋なら、その先行辺は同型。
方針：0の逆像の反映と全点の値から先行辺が値を保つと示し、実個数から同型へ戻す。
規約：実同型を新しい入力欄に置かない。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の非fillableな面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの深さの減少。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：0を反映する実射と底併合の合成が底併合の値を持てば、前半は全点の値を保つ。
方針：0の点には最小元保存、正の点には0の反映と1減算の等式を使う。
規約：空の有限順序も含む。使われ方：Riehl–Verity §4.2の純粋な実合成の消去。 -/
lemma ordinalVal_eq_of_bottomMerge_comp_pure {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hf : ∀ i, i.val = 1 → (f i).val ≠ 0)
    (hg : ∀ i, (g i).val = i.val - 1)
    (hcomp : ∀ i, (g.comp f i).val = i.val - 1) : ∀ i, (f i).val = i.val := by
  intro i
  by_cases hi : i.val = 0
  · exact (h0 i hi).trans hi.symm
  · have hn : (f i).val ≠ 0 := fun hz => hi (ordinalReflectsZero_of_no_one f hf i hz)
    have he := hcomp i
    change (g (f i)).val = i.val - 1 at he
    rw [hg] at he
    omega

/-- 概要：二点以上からの実非併合辺と純粋な実併合の合成が純粋なら、前半は実同型。
方針：実個数を等しくし、全点の値の保存から像の個数と変化量0を回収する。
規約：元の実Homの同型性を結論にする。使われ方：Riehl–Verity §4.2の非純粋性の検収。 -/
lemma walkingAdjunctionIsIso_of_pure_bottomMerge_comp {Y : WalkingAdjunctionPoint}
    {A B C : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (g : B ⟶ C)
    (ha : 2 ≤ walkingAdjunctionOrdinalCard .minus Y A)
    (hbc : walkingAdjunctionOrdinalCard .minus Y C + 1 =
      walkingAdjunctionOrdinalCard .minus Y B)
    (hf : ∀ i, i.val = 1 → (walkingAdjunctionOrderHom f i).val ≠ 0)
    (hg : ∀ i, (walkingAdjunctionOrderHom g i).val = i.val - 1)
    (hp : walkingAdjunctionOrdinalCard .minus Y C =
        walkingAdjunctionOrdinalCard .minus Y A - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom (f ≫ g) i).val = i.val - 1) : IsIso f := by
  have hv := ordinalVal_eq_of_bottomMerge_comp_pure (walkingAdjunctionOrderHom f)
    (walkingAdjunctionOrderHom g) (walkingAdjunctionOrderHom_bottom f) hf hg
    (by simpa only [walkingAdjunctionOrderHom_comp] using hp.2)
  have hi : Function.Injective (walkingAdjunctionOrderHom f) := by
    intro i j hij
    apply Fin.ext
    exact (hv i).symm.trans ((congrArg Fin.val hij).trans (hv j))
  have hr := (ordinalImageCard_eq_source_iff (walkingAdjunctionOrderHom f)).mpr hi
  apply (walkingAdjunctionMapVariation_zero_iff_isIso f).mp
  unfold ordinalMapVariation
  rw [hr]
  have hc := hp.1
  omega

end SerrePositivity.InfinityCategories.HA.Monads
