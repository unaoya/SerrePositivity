module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedLeftProper
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanPushoutComparison

/-!
# 境界も動くpushout cubeの比較が局所化で可逆となる

## 概要
境界も動くpushout cubeの比較が局所化で可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0430][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0430
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Gluing a cube of actual pushouts with moving boundary

The three input comparisons can be nonmonos. Only one attaching leg in
each row is mono; the other attaching legs are arbitrary. The conclusion
concerns the original specified comparison of the two pushout objects.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanPushoutCube
variable {A B C P A' B' C' P' : SSet.{v}}
  (i : A ⟶ B) (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
  (i' : A' ⟶ B') (j' : A' ⟶ C') (u' : B' ⟶ P') (g' : C' ⟶ P')
  (sq' : IsPushout i' j' u' g') [Mono i] [Mono i']
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (m : P ⟶ P')
  (hab : i ≫ b = a ≫ i') (hac : j ≫ c = a ≫ j')
  (hbm : u ≫ m = b ≫ u') (hcm : g ≫ m = c ≫ g')
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hb : IsIso (AnodyneHomotopy.anodyneQ.map b))
  (hc : IsIso (AnodyneHomotopy.anodyneQ.map c))

include sq sq' hab hac hbm hcm ha hb hc in
/-- 境界も動くpushout cubeの比較が局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map m) := by
  let v := pushout.inl i (j ≫ c)
  let w := pushout.inr i (j ≫ c)
  let d := sq.desc v (c ≫ w) (by
    rw [← Category.assoc]
    exact pushout.condition)
  have hud : u ≫ d = v := sq.inl_desc _ _ _
  have hgd : g ≫ d = c ≫ w := sq.inr_desc _ _ _
  have hdSq : IsPushout c g w d := by
    have ho : IsPushout (j ≫ c) i w (u ≫ d) := by
      rw [hud]
      exact (IsPushout.of_hasPushout i (j ≫ c)).flip
    exact ho.of_left hgd.symm sq.flip
  have : Mono g := (MorphismProperty.monomorphisms SSet.{v}).of_isPushout sq.flip inferInstance
  have hd : IsIso (AnodyneHomotopy.anodyneQ.map d) :=
    KanLocalizedLeftProper.localized_isIso c hc g w d hdSq
  let l := pushout.inl i a
  let k := pushout.inr i a
  have : Mono k := (MorphismProperty.monomorphisms SSet.{v}).pushout_inr i a inferInstance
  have hl : IsIso (AnodyneHomotopy.anodyneQ.map l) :=
    KanLocalizedLeftProper.localized_isIso a ha i k l (IsPushout.of_hasPushout i a).flip
  let e := pushout.desc (f := i) (g := a) b i' hab
  have hle : l ≫ e = b := pushout.inl_desc _ _ _
  have hke : k ≫ e = i' := pushout.inr_desc _ _ _
  have he : IsIso (AnodyneHomotopy.anodyneQ.map e) := by
    have : IsIso (AnodyneHomotopy.anodyneQ.map l) := hl
    have h := congrArg AnodyneHomotopy.anodyneQ.map hle
    rw [CategoryTheory.Functor.map_comp] at h
    exact (isIso_comp_left_iff _ _).mp (h.symm ▸ hb)
  let z := pushout.desc (f := i) (g := a) v (j' ≫ w) (by
    rw [← Category.assoc, ← hac]
    exact pushout.condition)
  have hlz : l ≫ z = v := pushout.inl_desc _ _ _
  have hkz : k ≫ z = j' ≫ w := pushout.inr_desc _ _ _
  have hzSq : IsPushout k j' z w := by
    have ho : IsPushout i (a ≫ j') (l ≫ z) w := by
      rw [hlz, ← hac]
      exact IsPushout.of_hasPushout _ _
    exact ho.of_top hkz (IsPushout.of_hasPushout i a)
  let n := pushout.desc (f := i) (g := j ≫ c) (b ≫ u') g' (by
    rw [← Category.assoc, hab, Category.assoc, sq'.w, ← Category.assoc, ← hac])
  have hvn : v ≫ n = b ≫ u' := pushout.inl_desc _ _ _
  have hwn : w ≫ n = g' := pushout.inr_desc _ _ _
  have hzn : z ≫ n = e ≫ u' := by
    apply (IsPushout.of_hasPushout i a).hom_ext
    · change l ≫ (z ≫ n) = l ≫ (e ≫ u')
      rw [← Category.assoc, hlz, hvn, ← Category.assoc, hle]
    · change k ≫ (z ≫ n) = k ≫ (e ≫ u')
      rw [← Category.assoc, hkz, Category.assoc, hwn, ← Category.assoc, hke]
      exact sq'.w.symm
  have hn : IsIso (AnodyneHomotopy.anodyneQ.map n) :=
    KanPushoutComparison.actual_localized_isIso j' k i' e hke he z w hzSq
      u' g' sq' n hzn hwn
  have hdn : d ≫ n = m := by
    apply sq.hom_ext
    · rw [← Category.assoc, hud, hvn, hbm]
    · rw [← Category.assoc, hgd, Category.assoc, hwn, hcm]
  have h := congrArg AnodyneHomotopy.anodyneQ.map hdn
  rw [CategoryTheory.Functor.map_comp] at h
  exact h ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map d ≫
    AnodyneHomotopy.anodyneQ.map n))

include sq sq' hab hac hbm hcm ha hb hc in
lemma image_isIso {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map m) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL m
    (localized_isIso i j u g sq i' j' u' g' sq' a b c m hab hac hbm hcm ha hb hc)

end SerrePositivity.SimplicialModel.KanPushoutCube
