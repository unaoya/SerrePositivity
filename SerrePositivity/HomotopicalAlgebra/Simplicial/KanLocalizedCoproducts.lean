module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestLiftingClass
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# 局所化で可逆な射の実際の余積もモデル構造を仮定せず局所化で可逆となる

## 概要
局所化で可逆な射の実際の余積もモデル構造を仮定せず局所化で可逆となる。
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
[棚卸し m0417][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0417
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Coproducts of arbitrary localized equivalences, without a value model structure

Fixed lifting tests handle coproducts of mono equivalences. The pointwise
Brown factorization then removes the mono hypothesis on all comparisons.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanLocalizedCoproducts
open KanTestLiftingClass MonoLocalizedFactorization

lemma coproduct_mem (W : MorphismProperty SSet.{v}) (I : Type w)
    [W.IsStableUnderCoproductsOfShape I] {A B : I → SSet.{v}}
    [HasCoproduct A] [HasCoproduct B] (f : ∀ i, A i ⟶ B i) (hf : ∀ i, W (f i)) :
    W (Limits.Sigma.map f) :=
  MorphismProperty.IsStableUnderColimitsOfShape.condition
    (Discrete.functor A) (Discrete.functor B)
    (Cofan.mk _ (Limits.Sigma.ι A)) (Cofan.mk _ (Limits.Sigma.ι B))
    (coproductIsCoproduct A) (coproductIsCoproduct B) (Discrete.natTrans (fun i => f i.as))
    (fun i => hf i.as) (Limits.Sigma.map f) (fun i => Limits.Sigma.ι_map f i.as)

lemma mono_localized_isIso (I : Type w) [Small.{v} I] {A B : I → SSet.{v}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, localizedMonos (f i)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map f)) := by
  have hl : rightTests.llp (Limits.Sigma.map f) :=
    coproduct_mem rightTests.llp I f (fun i => localizedMono_le_llp _ (hf i))
  exact localized_isIso_of_llp _ hl

lemma localized_isIso (I : Type w) [Small.{v} I] {A B : I → SSet.{v}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (f i))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map f)) := by
  let c := fun i => coprod.desc (f i) (𝟙 (B i))
  let l := fun i => coprod.inl ≫ left (c i)
  let r := fun i => coprod.inr ≫ left (c i)
  let p := fun i => right (c i)
  have hlp : ∀ i, l i ≫ p i = f i := by
    intro i
    dsimp only [l, p]
    rw [Category.assoc, fac]
    exact coprod.inl_desc _ _
  have hrp : ∀ i, r i ≫ p i = 𝟙 (B i) := by
    intro i
    dsimp only [r, p]
    rw [Category.assoc, fac]
    exact coprod.inr_desc _ _
  have hl : ∀ i, localizedMonos (l i) := by
    intro i
    have : Mono (coprod.inl : A i ⟶ A i ⨿ B i) :=
      (MorphismProperty.monomorphisms SSet.{v}).of_isPushout
        (IsPushout.of_hasBinaryCoproduct' (A i) (B i)) inferInstance
    have hm : Mono (l i) := by dsimp only [l]; infer_instance
    have : IsIso (AnodyneHomotopy.anodyneQ.map (p i)) := right_localized_isIso (c i)
    have h := congrArg AnodyneHomotopy.anodyneQ.map (hlp i)
    rw [CategoryTheory.Functor.map_comp] at h
    exact ⟨hm, (isIso_comp_right_iff _ _).mp (h.symm ▸ hf i)⟩
  have hr : ∀ i, localizedMonos (r i) := by
    intro i
    have : Mono (coprod.inr : B i ⟶ A i ⨿ B i) :=
      (MorphismProperty.monomorphisms SSet.{v}).of_isPushout
        (IsPushout.of_hasBinaryCoproduct' (A i) (B i)).flip inferInstance
    have hm : Mono (r i) := by dsimp only [r]; infer_instance
    have : IsIso (AnodyneHomotopy.anodyneQ.map (p i)) := right_localized_isIso (c i)
    have h := congrArg AnodyneHomotopy.anodyneQ.map (hrp i)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (r i) ≫
        AnodyneHomotopy.anodyneQ.map (p i)) := by rw [h]; infer_instance
    exact ⟨hm, (isIso_comp_right_iff _ _).mp hc⟩
  have : IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map l)) := mono_localized_isIso I l hl
  have : IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map r)) := mono_localized_isIso I r hr
  have hpr : Limits.Sigma.map r ≫ Limits.Sigma.map p = 𝟙 _ := by
    rw [Limits.Sigma.map_comp_map]
    simp only [hrp, Limits.Sigma.map_id]
  have : IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map p)) := by
    have h := congrArg AnodyneHomotopy.anodyneQ.map hpr
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map r) ≫
        AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map p)) := by rw [h]; infer_instance
    exact (isIso_comp_left_iff _ _).mp hc
  have hlf : Limits.Sigma.map l ≫ Limits.Sigma.map p = Limits.Sigma.map f := by
    rw [Limits.Sigma.map_comp_map]
    simp only [hlp]
  have h := congrArg AnodyneHomotopy.anodyneQ.map hlf
  rw [CategoryTheory.Functor.map_comp] at h
  exact h ▸ inferInstanceAs (IsIso (AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map l) ≫
    AnodyneHomotopy.anodyneQ.map (Limits.Sigma.map p)))

abbrev equivalences : MorphismProperty SSet.{v} :=
  (MorphismProperty.isomorphisms _).inverseImage AnodyneHomotopy.anodyneQ

instance stable (I : Type w) [Small.{v} I] :
    equivalences.{v}.IsStableUnderCoproductsOfShape I :=
  MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
    (fun _ _ _ _ f hf => localized_isIso I f hf)

/-- 局所化で可逆な射の実際の余積もモデル構造を仮定せず局所化で可逆となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma actual_localized_isIso (I : Type w) [Small.{v} I] {A B : I → SSet.{v}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsIso (AnodyneHomotopy.anodyneQ.map (f i)))
    (c : Cofan A) (c' : Cofan B) (hc : IsColimit c) (hc' : IsColimit c')
    (m : c.pt ⟶ c'.pt) (hm : ∀ i, c.inj i ≫ m = f i ≫ c'.inj i) :
    IsIso (AnodyneHomotopy.anodyneQ.map m) :=
  MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := equivalences) (Discrete.functor A) (Discrete.functor B) c c' hc hc'
    (Discrete.natTrans (fun i => f i.as)) (fun i => hf i.as) m (fun i => hm i.as)

end SerrePositivity.SimplicialModel.KanLocalizedCoproducts
