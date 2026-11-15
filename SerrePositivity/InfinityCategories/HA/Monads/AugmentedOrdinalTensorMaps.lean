module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalConcatenation
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionComposition

/-!
概要：混合Homで使う増大単体圏の順序和を、有限単調射の順序和と照合する。
方針：非空な因子の添字の輸送を先に解き、他方の空と非空を場合分けする。
規約：一方が非空であるという条件は混合Homの既存の対象の型から来る。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の残る混合水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：非空の因子の添字の輸送は元の順序和と同じ値。
方針：輸送で値が変わらないことと外延性を使う。
規約：型の違いはHEqで保持する。使われ方：Riehl–Verity Remark 3.3.8 の合成の照合。 -/
lemma ordinalAppendNonempty_heq {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) : HEq (ordinalAppendNonempty f g) (ordinalAppend f g) := by
  apply ordinalHom_hext (by omega) (by omega)
  intro i j hij
  let k : Fin ((m + 1) + p) := ⟨i.val, by have := i.isLt; omega⟩
  have hk : k = j := Fin.ext hij
  exact (ordinalAppendNonempty_val f g i).trans
    (congrArg (fun a => (ordinalAppend f g a).val) hk)

/-- 概要：既存の非空の単体の順序和は元の有限単調射の順序和。
方針：同じ実射の照合と添字の輸送を合わせる。
規約：値の式だけでなく全写像を比較する。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma simplexTensorHomOf_append_heq {X Y Z W : SimplexCategory} (f : X ⟶ Y) (g : Z ⟶ W) :
    HEq (AugmentedSimplexCategory.tensorHomOf f g).toOrderHom
      (ordinalAppend f.toOrderHom g.toOrderHom) := by
  rw [simplexTensorHomOf_append]
  exact ordinalAppendNonempty_heq _ _

/-- 概要：右因子が非空の増大単体圏の全順序和の射を比較する。
方針：左因子の空と非空を分け、空からの射では右包含の値を計算する。
規約：左因子は空から非空への射も含む。使われ方：HA Proposition 4.7.3.3 の左作用。 -/
lemma augmentedOrderHom_tensor_nonempty_right {A B : AugmentedSimplexCategory}
    {C D : SimplexCategory} (f : A ⟶ B) (g : C ⟶ D) :
    HEq (augmentedOrderHom (f ⊗ₘ WithInitial.incl.map g))
      (ordinalAppend (augmentedOrderHom f) g.toOrderHom) := by
  cases A with
  | star =>
    cases B with
    | star =>
      change HEq g.toOrderHom (ordinalAppend (augmentedOrderHom f) g.toOrderHom)
      apply ordinalHom_hext
        (by change C.len + 1 = 0 + (C.len + 1); omega)
        (by change D.len + 1 = 0 + (D.len + 1); omega)
      intro i j hij
      have hk : (⟨j.val, by have := i.isLt; omega⟩ : Fin (C.len + 1)) = i :=
        Fin.ext hij.symm
      have hv := ordinalAppend_val_right (augmentedOrderHom f) g.toOrderHom j (Nat.zero_le _)
      simpa only [Nat.zero_add, Nat.sub_zero, hk] using hv.symm
    | of b =>
      change HEq (g ≫ AugmentedSimplexCategory.inr' b D).toOrderHom
        (ordinalAppend (augmentedOrderHom f) g.toOrderHom)
      apply ordinalHom_hext
        (by change C.len + 1 = 0 + (C.len + 1); omega)
        (by change b.len + D.len + 1 + 1 = (b.len + 1) + (D.len + 1); omega)
      intro i j hij
      have hk : (⟨j.val, by have := i.isLt; omega⟩ : Fin (C.len + 1)) = i :=
        Fin.ext hij.symm
      have hv := ordinalAppend_val_right (augmentedOrderHom f) g.toOrderHom j (Nat.zero_le _)
      have hl : ((g ≫ AugmentedSimplexCategory.inr' b D).toOrderHom i).val =
          (b.len + 1) + (g.toOrderHom i).val := by
        change ((AugmentedSimplexCategory.inr' b D).toOrderHom (g.toOrderHom i)).val = _
        simp only [AugmentedSimplexCategory.inr'_eval, Fin.val_cast, Fin.val_natAdd]
      calc
        _ = (b.len + 1) + (g.toOrderHom i).val := hl
        _ = _ := by simpa only [Nat.sub_zero, hk] using hv.symm
  | of a =>
    cases B with
    | star => cases f
    | of b => exact simplexTensorHomOf_append_heq f g

/-- 概要：左因子が非空の増大単体圏の全順序和の射を比較する。
方針：右因子の空と非空を分け、空からの射では左包含の値を使う。
規約：右因子の空から非空への射も残す。使われ方：HA Proposition 4.7.3.3 の右作用。 -/
lemma augmentedOrderHom_tensor_nonempty_left {A B : AugmentedSimplexCategory}
    {C D : SimplexCategory} (f : C ⟶ D) (g : A ⟶ B) :
    HEq (augmentedOrderHom (WithInitial.incl.map f ⊗ₘ g))
      (ordinalAppend f.toOrderHom (augmentedOrderHom g)) := by
  cases A with
  | star =>
    cases B with
    | star =>
      change HEq f.toOrderHom (ordinalAppend f.toOrderHom (augmentedOrderHom g))
      apply ordinalHom_hext
        (by change C.len + 1 = C.len + 1 + 0; omega)
        (by change D.len + 1 = D.len + 1 + 0; omega)
      intro i j hij
      have hj : j.val < C.len + 1 := by have := i.isLt; omega
      have hk : (⟨j.val, hj⟩ : Fin (C.len + 1)) = i := Fin.ext hij.symm
      have hv := ordinalAppend_val_left f.toOrderHom (augmentedOrderHom g) j hj
      simpa only [hk] using hv.symm
    | of b =>
      change HEq (f ≫ AugmentedSimplexCategory.inl' D b).toOrderHom
        (ordinalAppend f.toOrderHom (augmentedOrderHom g))
      apply ordinalHom_hext
        (by change C.len + 1 = C.len + 1 + 0; omega)
        (by change D.len + b.len + 1 + 1 = (D.len + 1) + (b.len + 1); omega)
      intro i j hij
      have hj : j.val < C.len + 1 := by have := i.isLt; omega
      have hk : (⟨j.val, hj⟩ : Fin (C.len + 1)) = i := Fin.ext hij.symm
      have hv := ordinalAppend_val_left f.toOrderHom (augmentedOrderHom g) j hj
      have hl : ((f ≫ AugmentedSimplexCategory.inl' D b).toOrderHom i).val =
          (f.toOrderHom i).val := by
        change ((AugmentedSimplexCategory.inl' D b).toOrderHom (f.toOrderHom i)).val = _
        simp only [AugmentedSimplexCategory.inl'_eval, Fin.val_cast, Fin.val_castAdd]
      exact hl.trans (by simpa only [hk] using hv.symm)
  | of a =>
    cases B with
    | star => cases g
    | of b => exact simplexTensorHomOf_append_heq f g

/-- 概要：増大単体圏の全順序和の射は有限単調射の順序和と一致する。
方針：一方が非空なら上の照合を使い、両方空なら空の点を除去する。
規約：空から非空への射も両方空の対象も含む。使われ方：HA Proposition 4.7.3.3 の全合成。 -/
lemma augmentedOrderHom_tensor {A B C D : AugmentedSimplexCategory}
    (f : A ⟶ B) (g : C ⟶ D) :
    HEq (augmentedOrderHom (f ⊗ₘ g))
      (ordinalAppend (augmentedOrderHom f) (augmentedOrderHom g)) := by
  cases A with
  | star =>
    cases C with
    | star =>
      apply ordinalHom_hext (by rfl) (augmentedOrdinalCard_tensor B D)
      intro i j hij
      exact Fin.elim0 i
    | of c =>
      cases D with
      | star => cases g
      | of d => exact augmentedOrderHom_tensor_nonempty_right f g
  | of a =>
    cases B with
    | star => cases f
    | of b => exact augmentedOrderHom_tensor_nonempty_left f g

end SerrePositivity.InfinityCategories.HA.Monads
