module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMerge

/-!
概要：実併合射の異なる両対象と、右合成の消去・残余射の一意性を照合する。
方針：一つ減る点の個数、実切断の全射性、共通表示の忠実性を使う。
規約：右因子の一意性を仮定せず元の実射の等式で証明する。
使われ方：Riehl–Verity §4.1–§4.2のfillableな原子の親の実構成、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限順序の併合は全射。
方針：構成済みの実切断から各点の逆像を取る。規約：全ての点。
使われ方：Riehl–Verity §4.1の併合後の残余射の一意性。 -/
lemma ordinalBottomMerge_surjective (m : ℕ) : Function.Surjective (ordinalBottomMerge m) := by
  intro i
  exact ⟨ordinalBottomMergeSection m i,
    congrArg (fun f : Fin (m + 1) →o Fin (m + 1) => f i) (ordinalBottomMerge_section m)⟩

/-- 概要：個数の等式による有限単調射の輸送は全射性を保つ。
方針：個数を同一視する。規約：同じ実射の係数移送。
使われ方：Riehl–Verity §4.1の元の実Homの併合の表示。 -/
lemma ordinalOrderHomTransport_surjective {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    (f : Fin a →o Fin b) (hf : Function.Surjective f) :
    Function.Surjective (ordinalOrderHomTransport hac hbd f) := by
  subst c
  subst d
  exact hf

/-- 概要：実併合射の共通表示は全射。
方針：有限順序の併合の全射性を個数の等式で移す。規約：元の実射の共通表示。
使われ方：Riehl–Verity §4.1の全射の消去。 -/
lemma walkingAdjunctionBottomMergeArrow_surjective {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    Function.Surjective (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA)) := by
  rw [walkingAdjunctionBottomMergeArrow_profile]
  exact ordinalOrderHomTransport_surjective _ _ _ (ordinalBottomMerge_surjective m)

/-- 概要：併合前と併合後の実対象は異なる。
方針：実点の個数が一つ減ることを使う。規約：対象の等式の否定。
使われ方：Riehl–Verity §4.1の細分後の最初の射の非退化性。 -/
lemma walkingAdjunctionBottomMergeObject_ne {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    A ≠ walkingAdjunctionBottomMergeObject Y m := by
  intro he
  have hc := congrArg (walkingAdjunctionOrdinalCard .minus Y) he
  rw [hA, walkingAdjunctionBottomMergeObject_card] at hc
  omega

/-- 概要：実併合射との右因子の合成は右因子を区別する。
方針：共通表示の全射性と忠実性で元の全射の等式を回収する。
規約：元のHom内の任意の右因子。使われ方：Riehl–Verity §4.1の実細分の一意性。 -/
lemma walkingAdjunctionBottomMergeArrow_cancel {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    {B : walkingAdjunctionHom .minus Y} (f g : walkingAdjunctionBottomMergeObject Y m ⟶ B)
    (h : walkingAdjunctionBottomMergeArrow A m hA ≫ f =
      walkingAdjunctionBottomMergeArrow A m hA ≫ g) : f = g := by
  apply walkingAdjunctionOrderHom_injective
  apply OrderHom.ext
  funext i
  obtain ⟨k, hk⟩ := walkingAdjunctionBottomMergeArrow_surjective A m hA i
  have hc := congrArg (fun q => walkingAdjunctionOrderHom q) h
  rw [walkingAdjunctionOrderHom_comp, walkingAdjunctionOrderHom_comp] at hc
  have he := congrArg (fun q => q k) hc
  change walkingAdjunctionOrderHom f
      (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) k) =
    walkingAdjunctionOrderHom g
      (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA) k) at he
  simpa only [hk] using he

/-- 概要：実併合後の右因子は構成した実残余射に一意に一致する。
方針：元の射との合成の等式と右因子の消去則を使う。
規約：右因子の存在・一意性を仮定しない。使われ方：Riehl–Verity §4.1の実親の照合。 -/
lemma walkingAdjunctionBottomMergeResidual_unique {Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom .minus Y} (f : A ⟶ B) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y A),
      i.val = 1 → (walkingAdjunctionOrderHom f i).val = 0)
    (g : walkingAdjunctionBottomMergeObject Y m ⟶ B)
    (hg : walkingAdjunctionBottomMergeArrow A m hA ≫ g = f) :
    g = walkingAdjunctionBottomMergeResidual f m hA h1 := by
  apply walkingAdjunctionBottomMergeArrow_cancel A m hA
  exact hg.trans (walkingAdjunctionBottomMerge_factor f m hA h1).symm

end SerrePositivity.InfinityCategories.HA.Monads
