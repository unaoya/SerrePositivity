module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionMapRepresentation

/-!
概要：walking adjunctionの混合した三重水平合成の結合則を証明する。
方針：忠実な有限単調射の表示で順序和と端点共有の結合則へ移す。
規約：全ての射を比較する。使われ方：HA Proposition 4.7.3.3、
Riehl–Verity Remark 3.3.8、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：既存のAppendの係数移送は射の異種等式を保つ。
方針：係数と射を同一視する。規約：同じ構成。
使われ方：Riehl–Verity Remark 3.3.8 の水平結合則。 -/
lemma ordinalAppend_heq {m n p q m' n' p' q' : ℕ}
    (hm : m = m') (hn : n = n') (hp : p = p') (hq : q = q')
    {f : Fin (m) →o Fin (n)} {f' : Fin (m') →o Fin (n')}
    {g : Fin (p) →o Fin (q)} {g' : Fin (p') →o Fin (q')}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (ordinalAppend f g) (ordinalAppend f' g') := by
  subst m'
  subst n'
  subst p'
  subst q'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- 概要：既存のGlueの係数移送は射の異種等式を保つ。
方針：係数と射を同一視する。規約：同じ構成。
使われ方：Riehl–Verity Remark 3.3.8 の水平結合則。 -/
lemma ordinalGlue_heq {m n p q m' n' p' q' : ℕ}
    (hm : m = m') (hn : n = n') (hp : p = p') (hq : q = q')
    {f : Fin (m + 1) →o Fin (n + 1)} {f' : Fin (m' + 1) →o Fin (n' + 1)}
    {g : Fin (p + 1) →o Fin (q + 1)} {g' : Fin (p' + 1) →o Fin (q' + 1)}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (ordinalGlue f g) (ordinalGlue f' g') := by
  subst m'
  subst n'
  subst p'
  subst q'
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

/-- 概要：plusを経由して入る合成の区間の次元。
方針：点の個数の加法則から1を除く。規約：元の合成の対象。
使われ方：Riehl–Verity Remark 3.3.8 の係数移送。 -/
lemma walkingAdjunctionIncomingDim_comp_plus (X : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X .plus) (B : walkingAdjunctionHom .plus .minus) :
    walkingAdjunctionIncomingDim X ((walkingAdjunctionHorizontal X .plus .minus).obj (A, B)) =
      walkingAdjunctionOrdinalCard X .plus A + walkingAdjunctionIncomingDim .plus B := by
  have h := walkingAdjunctionOrdinalCard_comp_plus X .minus A B
  have h₁ := walkingAdjunctionIncoming_card X
    ((walkingAdjunctionHorizontal X .plus .minus).obj (A, B))
  have h₂ := walkingAdjunctionIncoming_card .plus B
  omega

/-- 概要：plusを経由して出る合成の区間の次元。
方針：点の個数の加法則から1を除く。規約：元の合成の対象。
使われ方：Riehl–Verity Remark 3.3.8 の係数移送。 -/
lemma walkingAdjunctionOutgoingDim_comp_plus (Z : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom .minus .plus) (B : walkingAdjunctionHom .plus Z) :
    walkingAdjunctionOutgoingDim Z ((walkingAdjunctionHorizontal .minus .plus Z).obj (A, B)) =
      walkingAdjunctionOutgoingDim .plus A + walkingAdjunctionOrdinalCard .plus Z B := by
  have h := walkingAdjunctionOrdinalCard_comp_plus .minus Z A B
  have h₁ := walkingAdjunctionOutgoing_card Z
    ((walkingAdjunctionHorizontal .minus .plus Z).obj (A, B))
  have h₂ := walkingAdjunctionOutgoing_card .plus A
  omega

variable {I : Type*} [Category I]

/-- 概要：中央がplus・minusとなる全三重水平合成の結合則。
方針：全射を順序和と端点共有の結合則へ移す。
規約：任意の添字圏上の全関手。使われ方：HA Proposition 4.7.3.3 のwalking adjunction。 -/
lemma walkingAdjunctionHorizontal_assoc_plus_minus (X Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X .plus)
    (G : I ⥤ walkingAdjunctionHom .plus .minus)
    (H : I ⥤ walkingAdjunctionHom .minus Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal X .plus .minus).prod' H ⋙
        walkingAdjunctionHorizontal X .minus Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .plus .minus Z) ⋙
        walkingAdjunctionHorizontal X .plus Z) := by
  apply CategoryTheory.Functor.hext
  · intro i
    exact walkingAdjunctionHorizontal_obj_assoc X .plus .minus Z (F.obj i) (G.obj i) (H.obj i)
  · intro i j a
    apply walkingAdjunctionOrderHom_hext
      (walkingAdjunctionHorizontal_obj_assoc X .plus .minus Z (F.obj i) (G.obj i) (H.obj i))
      (walkingAdjunctionHorizontal_obj_assoc X .plus .minus Z (F.obj j) (G.obj j) (H.obj j))
    let f := F.map a
    let g := G.map a
    let h := H.map a
    let fg := (walkingAdjunctionHorizontal X .plus .minus).map
      (X := (F.obj i, G.obj i)) (Y := (F.obj j, G.obj j)) (f, g)
    let gh := (walkingAdjunctionHorizontal .plus .minus Z).map
      (X := (G.obj i, H.obj i)) (Y := (G.obj j, H.obj j)) (g, h)
    have hfg := (walkingAdjunctionIncomingMap_heq (X := X) fg).trans
      (walkingAdjunctionOrderHom_comp_plus X .minus f g)
    have hgh := walkingAdjunctionOrderHom_comp_minus .plus Z g h
    have hl := walkingAdjunctionOrderHom_comp_minus X Z fg h
    have hr := walkingAdjunctionOrderHom_comp_plus X Z f gh
    have hl' := ordinalGlue_heq
      (walkingAdjunctionIncomingDim_comp_plus X (F.obj i) (G.obj i))
      (walkingAdjunctionIncomingDim_comp_plus X (F.obj j) (G.obj j)) rfl rfl
      hfg (HEq.refl (walkingAdjunctionOutgoingMap (Y := Z) h))
    have hr' := ordinalAppend_heq rfl rfl
      (walkingAdjunctionOrdinalCard_comp_minus .plus Z (G.obj i) (H.obj i))
      (walkingAdjunctionOrdinalCard_comp_minus .plus Z (G.obj j) (H.obj j))
      (HEq.refl (walkingAdjunctionOrderHom (X := X) (Y := .plus) f)) hgh
    exact hl.trans (hl'.trans ((ordinalAppend_glue_assoc
      (walkingAdjunctionOrderHom (X := X) (Y := .plus) f)
      (walkingAdjunctionIncomingMap (X := .plus) g)
      (walkingAdjunctionOutgoingMap (Y := Z) h)).trans (hr.trans hr').symm))

/-- 概要：中央がminus・plusとなる全三重水平合成の結合則。
方針：端点共有と順序和の全射の結合則を忠実な表示から戻す。
規約：任意の添字圏。使われ方：HA Proposition 4.7.3.3 のwalking adjunction。 -/
lemma walkingAdjunctionHorizontal_assoc_minus_plus (X Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X .minus)
    (G : I ⥤ walkingAdjunctionHom .minus .plus)
    (H : I ⥤ walkingAdjunctionHom .plus Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal X .minus .plus).prod' H ⋙
        walkingAdjunctionHorizontal X .plus Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal .minus .plus Z) ⋙
        walkingAdjunctionHorizontal X .minus Z) := by
  apply CategoryTheory.Functor.hext
  · intro i
    exact walkingAdjunctionHorizontal_obj_assoc X .minus .plus Z (F.obj i) (G.obj i) (H.obj i)
  · intro i j a
    apply walkingAdjunctionOrderHom_hext
      (walkingAdjunctionHorizontal_obj_assoc X .minus .plus Z (F.obj i) (G.obj i) (H.obj i))
      (walkingAdjunctionHorizontal_obj_assoc X .minus .plus Z (F.obj j) (G.obj j) (H.obj j))
    let f := F.map a
    let g := G.map a
    let h := H.map a
    let fg := (walkingAdjunctionHorizontal X .minus .plus).map
      (X := (F.obj i, G.obj i)) (Y := (F.obj j, G.obj j)) (f, g)
    let gh := (walkingAdjunctionHorizontal .minus .plus Z).map
      (X := (G.obj i, H.obj i)) (Y := (G.obj j, H.obj j)) (g, h)
    have hfg := walkingAdjunctionOrderHom_comp_minus X .plus f g
    have hgh := (walkingAdjunctionOutgoingMap_heq (Y := Z) gh).trans
      (walkingAdjunctionOrderHom_comp_plus .minus Z g h)
    have hgh' := hgh.trans (ordinalAppendNonempty_heq
      (walkingAdjunctionOutgoingMap (Y := .plus) g)
      (walkingAdjunctionOrderHom (X := .plus) (Y := Z) h)).symm
    have hl := walkingAdjunctionOrderHom_comp_plus X Z fg h
    have hr := walkingAdjunctionOrderHom_comp_minus X Z f gh
    have hl' := ordinalAppend_heq
      (walkingAdjunctionOrdinalCard_comp_minus X .plus (F.obj i) (G.obj i))
      (walkingAdjunctionOrdinalCard_comp_minus X .plus (F.obj j) (G.obj j)) rfl rfl
      hfg (HEq.refl (walkingAdjunctionOrderHom (X := .plus) (Y := Z) h))
    have hr' := ordinalGlue_heq rfl rfl
      (walkingAdjunctionOutgoingDim_comp_plus Z (G.obj i) (H.obj i))
      (walkingAdjunctionOutgoingDim_comp_plus Z (G.obj j) (H.obj j))
      (HEq.refl (walkingAdjunctionIncomingMap (X := X) f)) hgh'
    have hn := ordinalAppendNonempty_heq
      (ordinalGlue (walkingAdjunctionIncomingMap (X := X) f)
        (walkingAdjunctionOutgoingMap (Y := .plus) g))
      (walkingAdjunctionOrderHom (X := .plus) (Y := Z) h)
    exact hl.trans (hl'.trans (hn.symm.trans ((ordinalGlue_append_assoc
      (walkingAdjunctionIncomingMap (X := X) f)
      (walkingAdjunctionOutgoingMap (Y := .plus) g)
      (walkingAdjunctionOrderHom (X := .plus) (Y := Z) h)).trans (hr.trans hr').symm)))

/-- 概要：walking adjunctionの十六通りの全水平結合則。
方針：中央の二点で分類し、八つの既存の法則と二つの一般形へ帰着する。
規約：対象だけでなく全関手の等式。使われ方：HA Proposition 4.7.3.3 の添字の豊穣圏。 -/
lemma walkingAdjunctionHorizontal_assoc (W X Y Z : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom W X) (G : I ⥤ walkingAdjunctionHom X Y)
    (H : I ⥤ walkingAdjunctionHom Y Z) :
    ((F.prod' G ⋙ walkingAdjunctionHorizontal W X Y).prod' H ⋙
        walkingAdjunctionHorizontal W Y Z) =
      (F.prod' (G.prod' H ⋙ walkingAdjunctionHorizontal X Y Z) ⋙
        walkingAdjunctionHorizontal W X Z) := by
  cases X <;> cases Y
  · cases W <;> cases Z
    · exact ordinalSumFunctor_assoc F G H
    · exact topOrdinalActionFunctor_assoc F G H
    · exact bottomOrdinalActionFunctor_assoc F G H
    · exact mixedBottomTopFunctor_balance F G H
  · exact walkingAdjunctionHorizontal_assoc_plus_minus W Z F G H
  · exact walkingAdjunctionHorizontal_assoc_minus_plus W Z F G H
  · cases W <;> cases Z
    · exact mixedTopBottomFunctor_balance F G H
    · exact topOppositeOrdinalActionFunctor_assoc F G H
    · exact bottomOppositeOrdinalActionFunctor_assoc F G H
    · exact oppositeOrdinalSumFunctor_assoc F G H

end SerrePositivity.InfinityCategories.HA.Monads
