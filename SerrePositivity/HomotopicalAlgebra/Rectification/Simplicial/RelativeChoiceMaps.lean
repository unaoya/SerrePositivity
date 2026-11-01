module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace

/-!
# 中断した任意モデル源への一般化：RelativeChoiceMaps

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual transport maps between fixed-boundary comparison spaces。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0540][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0540
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual transport maps between fixed-boundary comparison spaces

Changing the codomain or restricting the source transports entire relative
comparison families as simplicial maps. All previously chosen parameter
faces are therefore retained. The evaluated family is the actual changed
family, not merely a homotopic replacement. No model structure is needed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace

lemma ofExtension_congr {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (e e' : T ⟶ P) (he : i ≫ e = b) (he' : i ≫ e' = b) (h : e = e') :
    ofExtension i b e he = ofExtension i b e' he' := by cases h; rfl

lemma name_postcomp {V P Q : SSet.{v}} (b : V ⟶ P) (q : P ⟶ Q) :
    name b ≫ (ihom V).map q = name (b ≫ q) := by
  rw [name, Category.assoc, curry'_ihom_map]

lemma restriction_comp {V T U P : SSet.{v}} (f : V ⟶ T) (g : T ⟶ U) :
    (MonoidalClosed.internalHom.map g.op).app P ≫ (MonoidalClosed.internalHom.map f.op).app P =
      (MonoidalClosed.internalHom.map (f ≫ g).op).app P :=
  (congr_app (MonoidalClosed.internalHom.map_comp g.op f.op) P).symm

def postMap {V T P Q : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
    (q : P ⟶ Q) (hq : b ≫ q = b') : obj i b ⟶ obj i b' :=
  pullback.lift (inclusion i b ≫ (ihom T).map q) (projection i b) (by
    have hn : (ihom T).map q ≫ (MonoidalClosed.internalHom.map i.op).app Q =
        (MonoidalClosed.internalHom.map i.op).app P ≫ (ihom V).map q :=
      (MonoidalClosed.internalHom.map i.op).naturality q
    rw [Category.assoc, hn, ← Category.assoc,
      over, Category.assoc, name_postcomp, hq])

@[reassoc (attr := simp)]
lemma postMap_inclusion {V T P Q : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
    (q : P ⟶ Q) (hq : b ≫ q = b') :
    postMap i b b' q hq ≫ inclusion i b' = inclusion i b ≫ (ihom T).map q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma postMap_projection {V T P Q : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
    (q : P ⟶ Q) (hq : b ≫ q = b') :
    postMap i b b' q hq ≫ projection i b' = projection i b := pullback.lift_snd _ _ _

lemma postMap_ofExtension {V T P Q : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
    (q : P ⟶ Q) (hq : b ≫ q = b') (e : T ⟶ P) (he : i ≫ e = b) :
    ofExtension i b e he ≫ postMap i b b' q hq =
      ofExtension i b' (e ≫ q) (by rw [← Category.assoc, he, hq]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, postMap_inclusion, ← Category.assoc, ofExtension_inclusion, name_postcomp]
    exact (ofExtension_inclusion i b' (e ≫ q) _).symm
  · rw [Category.assoc, postMap_projection, ofExtension_projection]
    exact (ofExtension_projection i b' (e ≫ q) _).symm

lemma family_postMap {V T P Q K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
    (q : P ⟶ Q) (hq : b ≫ q = b') (s : K ⟶ obj i b) :
    family i b' (s ≫ postMap i b b' q hq) = family i b s ≫ q := by
  rw [family, Category.assoc, postMap_inclusion, ← Category.assoc, uncurry_natural_right]

lemma postMap_identity {V T P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) :
    postMap i b b (𝟙 P) (Category.comp_id b) = 𝟙 (obj i b) := by
  apply pullback.hom_ext
  · rw [postMap_inclusion, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  · rw [postMap_projection, Category.id_comp]

lemma postMap_compose {V T P Q R : SSet.{v}} (i : V ⟶ T)
    (b : V ⟶ P) (b' : V ⟶ Q) (b'' : V ⟶ R) (q : P ⟶ Q) (r : Q ⟶ R)
    (hq : b ≫ q = b') (hr : b' ≫ r = b'') :
    postMap i b b' q hq ≫ postMap i b' b'' r hr =
      postMap i b b'' (q ≫ r) (by rw [← Category.assoc, hq, hr]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, postMap_inclusion, postMap_inclusion_assoc]
    rw [CategoryTheory.Functor.map_comp]
  · simp only [Category.assoc, postMap_projection]

def preMap {V T V' T' P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (i' : V' ⟶ T') (b' : V' ⟶ P)
    (v : V' ⟶ V) (t : T' ⟶ T) (hi : i' ≫ t = v ≫ i) (hb : v ≫ b = b') :
    obj i b ⟶ obj i' b' :=
  pullback.lift (inclusion i b ≫ (MonoidalClosed.internalHom.map t.op).app P) (projection i b) (by
    rw [Category.assoc, restriction_comp i' t, hi, ← restriction_comp v i, ← Category.assoc,
      over, Category.assoc, name_precomp, hb])

@[reassoc (attr := simp)]
lemma preMap_inclusion {V T V' T' P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (i' : V' ⟶ T') (b' : V' ⟶ P) (v : V' ⟶ V) (t : T' ⟶ T)
    (hi : i' ≫ t = v ≫ i) (hb : v ≫ b = b') :
    preMap i b i' b' v t hi hb ≫ inclusion i' b' =
      inclusion i b ≫ (MonoidalClosed.internalHom.map t.op).app P := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma preMap_projection {V T V' T' P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (i' : V' ⟶ T') (b' : V' ⟶ P) (v : V' ⟶ V) (t : T' ⟶ T)
    (hi : i' ≫ t = v ≫ i) (hb : v ≫ b = b') :
    preMap i b i' b' v t hi hb ≫ projection i' b' = projection i b := pullback.lift_snd _ _ _

lemma preMap_ofExtension {V T V' T' P : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (i' : V' ⟶ T') (b' : V' ⟶ P) (v : V' ⟶ V) (t : T' ⟶ T)
    (hi : i' ≫ t = v ≫ i) (hb : v ≫ b = b') (e : T ⟶ P) (he : i ≫ e = b) :
    ofExtension i b e he ≫ preMap i b i' b' v t hi hb =
      ofExtension i' b' (t ≫ e) (by rw [← Category.assoc, hi, Category.assoc, he, hb]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, preMap_inclusion, ← Category.assoc, ofExtension_inclusion, name_precomp]
    exact (ofExtension_inclusion i' b' (t ≫ e) _).symm
  · rw [Category.assoc, preMap_projection, ofExtension_projection]
    exact (ofExtension_projection i' b' (t ≫ e) _).symm

lemma family_preMap {V T V' T' P K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (i' : V' ⟶ T') (b' : V' ⟶ P) (v : V' ⟶ V) (t : T' ⟶ T)
    (hi : i' ≫ t = v ≫ i) (hb : v ≫ b = b') (s : K ⟶ obj i b) :
    family i' b' (s ≫ preMap i b i' b' v t hi hb) = t ▷ K ≫ family i b s := by
  rw [family, Category.assoc, preMap_inclusion, ← Category.assoc]
  exact uncurry_pre_app P (s ≫ inclusion i b) t

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
