module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightPushoutEquivalence
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutEquivalence

/-!
# 任意の局所化同値を単射に沿って押し出した射も局所化同値となる

## 概要
任意の局所化同値を単射に沿って押し出した射も局所化同値となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。

## 規約と注意
押し出す脚の単射性と比較射の局所化可逆性を仮定し、値モデルは要求しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0418][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0418
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Model-free left properness of the original anodyne localization

Every localized equivalence remains one after an actual pushout along a
mono. Boundary factorization reduces to the mono and boundary-right cases.
Neither the comparing map nor any original object is assumed Kan.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanLocalizedLeftProper
open MonoLocalizedFactorization
variable {A B C P : SSet.{v}} (f : A ⟶ B)
  (hf : IsIso (AnodyneHomotopy.anodyneQ.map f))
  (j : A ⟶ C) [Mono j] (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout f j u g)

include hf sq in
/-- 任意の局所化同値を単射に沿って押し出した射も局所化同値となる。

押し出す脚の単射性と比較射の局所化可逆性を仮定し、値モデルは要求しない。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map g) := by
  let i := left f
  let p := right f
  let u₁ := pushout.inl i j
  let g₁ := pushout.inr i j
  have hm : Mono u₁ := (MorphismProperty.monomorphisms SSet.{v}).pushout_inl i j inferInstance
  let t := pushout.desc (f := i) (g := j) (p ≫ u) g (by
    rw [← Category.assoc, fac]
    exact sq.w)
  have hu : u₁ ≫ t = p ≫ u := pushout.inl_desc _ _ _
  have hg : g₁ ≫ t = g := pushout.inr_desc _ _ _
  have ho : IsPushout (i ≫ p) j u (g₁ ≫ t) := by
    rw [hg, fac]
    exact sq
  have hs : IsPushout p u₁ u t := ho.of_left hu.symm (IsPushout.of_hasPushout i j)
  have h₁ : IsIso (AnodyneHomotopy.anodyneQ.map g₁) :=
    KanMonoPushoutEquivalence.localized_isIso i j u₁ g₁ (IsPushout.of_hasPushout i j)
      ((left_localized_isIso_iff f).mpr hf)
  have h₂ : IsIso (AnodyneHomotopy.anodyneQ.map t) :=
    MonoRightPushoutEquivalence.localized_isIso p (right_all_mono_rlp f) u₁ u t hs
  have he : AnodyneHomotopy.anodyneQ.map g₁ ≫ AnodyneHomotopy.anodyneQ.map t =
      AnodyneHomotopy.anodyneQ.map g :=
    (AnodyneHomotopy.anodyneQ.map_comp _ _).symm.trans
      (congrArg AnodyneHomotopy.anodyneQ.map hg)
  exact he ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map g₁ ≫
    AnodyneHomotopy.anodyneQ.map t))

include hf sq in
/-- anodyne射を反転する任意の関手で単射に沿うpushout比較の像が可逆となる。

押し出す脚の単射性と比較射の局所化可逆性を仮定し、値モデルは要求しない。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma image_isIso {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map g) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL g (localized_isIso f hf j u g sq)

end SerrePositivity.SimplicialModel.KanLocalizedLeftProper
