module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.UnderMonoBrown
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# 共通の始域の下で単射を持つ図式の局所化比較が実pushoutでも保たれる

## 概要
共通の始域の下で単射を持つ図式の局所化比較が実pushoutでも保たれる。
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
[棚卸し m0429][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0429
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Pushout comparison for localized equivalences between mono objects under A

The comparing map need not be mono. The base-change map is arbitrary.
Brown's argument applies to the actual undercategory pushout functor.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanPushoutComparison
variable {A T : SSet.{v}} (a : A ⟶ T)

lemma map_isPushout {X Y : Under A} (f : X ⟶ Y) :
    IsPushout f.right (pushout.inl X.hom a) (pushout.inl Y.hom a)
      (((Under.pushout a).map f).right) := by
  let g := ((Under.pushout a).map f).right
  have hl : pushout.inl X.hom a ≫ g = f.right ≫ pushout.inl Y.hom a := by
    dsimp only [g, Under.pushout]
    exact pushout.inl_desc _ _ _
  have hr : pushout.inr X.hom a ≫ g = pushout.inr Y.hom a := by
    dsimp only [g, Under.pushout]
    exact pushout.inr_desc _ _ _
  have ho : IsPushout (X.hom ≫ f.right) a (pushout.inl Y.hom a)
      (pushout.inr X.hom a ≫ g) := by
    rw [hr, f.w]
    exact IsPushout.of_hasPushout _ _
  exact ho.of_left hl.symm (IsPushout.of_hasPushout X.hom a)

lemma localized_isIso {X Y : Under A} [Mono X.hom] [Mono Y.hom] (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f.right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (((Under.pushout a).map f).right)) := by
  let F := Under.pushout a ⋙ Under.forget T ⋙ AnodyneHomotopy.anodyneQ
  apply UnderMonoBrown.map_isIso F (fun {X Y} h hm hw => ?_) f hf
  have : Mono h.right := hm
  exact KanMonoPushoutEquivalence.localized_isIso h.right (pushout.inl X.hom a)
    (pushout.inl Y.hom a) (((Under.pushout a).map h).right) (map_isPushout a h) hw

/-- 共通の始域の下で単射を持つ図式の局所化比較が実pushoutでも保たれる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma actual_localized_isIso {X Y P Q : SSet.{v}} (i : A ⟶ X) (j : A ⟶ Y)
    [Mono i] [Mono j] (f : X ⟶ Y) (hf : i ≫ f = j)
    (hw : IsIso (AnodyneHomotopy.anodyneQ.map f))
    (u : X ⟶ P) (v : T ⟶ P) (sq : IsPushout i a u v)
    (u' : Y ⟶ Q) (v' : T ⟶ Q) (sq' : IsPushout j a u' v')
    (m : P ⟶ Q) (hm : u ≫ m = f ≫ u') (hm' : v ≫ m = v') :
    IsIso (AnodyneHomotopy.anodyneQ.map m) := by
  let h : Under.mk i ⟶ Under.mk j := Under.homMk f hf
  let b := ((Under.pushout a).map h).right
  have : Mono (Under.mk i).hom := by change Mono i; infer_instance
  have : Mono (Under.mk j).hom := by change Mono j; infer_instance
  have hb : IsIso (AnodyneHomotopy.anodyneQ.map b) := localized_isIso a h hw
  have he : sq.isoPushout.hom ≫ b = m ≫ sq'.isoPushout.hom := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.inl_isoPushout_hom,
        ← Category.assoc, hm, Category.assoc, sq'.inl_isoPushout_hom]
      exact (map_isPushout a h).w.symm
    · rw [← Category.assoc, sq.inr_isoPushout_hom,
        ← Category.assoc, hm', sq'.inr_isoPushout_hom]
      dsimp only [b, Under.pushout]
      exact pushout.inr_desc _ _ _
  have hq := congrArg AnodyneHomotopy.anodyneQ.map he
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hq
  have : IsIso (AnodyneHomotopy.anodyneQ.map b) := hb
  have : IsIso (AnodyneHomotopy.anodyneQ.map m ≫
      AnodyneHomotopy.anodyneQ.map sq'.isoPushout.hom) := hq ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

end SerrePositivity.SimplicialModel.KanPushoutComparison
