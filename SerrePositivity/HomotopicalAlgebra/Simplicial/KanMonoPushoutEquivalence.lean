module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoPushoutExtension

/-!
# 局所化で可逆な単射のpushoutがモデル構造なしで局所化可逆となる

## 概要
局所化で可逆な単射のpushoutがモデル構造なしで局所化可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。

## 規約と注意
Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
ここでのKan条件は外側も含む全hornの充填であり、内側hornだけの条件ではない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論の加法性・局所化で現れる貼り合わせと余極限の比較に利用できる。
[棚卸し m0423][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0423
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Pushouts preserve localized mono equivalences without a value model structure

Both endpoints and the entire homotopy on the pushout leg are retained
when gluing intervals. Kan class injectivity and surjectivity then detect
the localized equivalence of the actual pushout morphism.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.KanMonoPushoutEquivalence
variable {A B C P K : SSet.{v}} (i : A ⟶ B) [Mono i]
  (j : A ⟶ C) (u : B ⟶ P) (g : C ⟶ P) (sq : IsPushout i j u g)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include sq hi hK in
lemma exists_homotopy (f f' : P ⟶ K) (H : SSet.Homotopy (g ≫ f) (g ≫ f')) :
    ∃ V : SSet.Homotopy f f',
      g ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h := by
  let HA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (HomotopyClasses.preHomotopy j H)
    (by rw [← Category.assoc, ← sq.w, Category.assoc])
    (by rw [← Category.assoc, ← sq.w, Category.assoc])
  obtain ⟨HB, hB⟩ := KanMonoRelativeHomotopy.exists_extension i hi hK (u ≫ f) (u ≫ f') HA
  have hc : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ HB.h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h := by
    rw [hB]
    dsimp only [HA]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h]
    rfl
  let tsq := sq.map (tensorRight (SSet.stdSimplex.obj (SimplexCategory.mk 1)))
  let q := tsq.desc HB.h H.h hc
  have hu : u ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q = HB.h :=
    tsq.inl_desc _ _ _
  have hg : g ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q = H.h :=
    tsq.inr_desc _ _ _
  refine ⟨{ h := q, h₀ := ?_, h₁ := ?_, rel := ?_ }, hg⟩
  · change SSet.ι₀ ≫ q = f
    apply sq.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hu, HB.h₀]
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hg, H.h₀]
  · change SSet.ι₁ ≫ q = f'
    apply sq.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hu, HB.h₁]
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hg, H.h₁]
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

include sq hi hK in
lemma pre_injective : Function.Injective (HomotopyClasses.pre g (K := K)) := by
  intro x y h
  obtain ⟨f, rfl⟩ := Quot.exists_rep x
  obtain ⟨f', rfl⟩ := Quot.exists_rep y
  obtain ⟨H⟩ := KanActualHomotopy.of_class_eq hK h
  obtain ⟨V, _⟩ := exists_homotopy i j u g sq hi hK f f' H
  exact HomotopyClasses.sound V

include sq hi in
lemma tests : KanTestDetection.Tests g := by
  intro K hK
  exact ⟨pre_injective i j u g sq hi hK,
    KanMonoPushoutExtension.pre_surjective i j u g sq hi hK⟩

include sq hi in
/-- 局所化で可逆な単射のpushoutがモデル構造なしで局所化可逆となる。

Kan条件・右持ち上げ性・単射性は各宣言で指定された範囲で用いる。
Kan値への実写像とホモトピー類のテストで比較射を調べる。
貼り合わせ・持ち上げとanodyne局所化の検出を使って像の可逆性を導く。
-/
lemma localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map g) :=
  (KanTestDetection.anodyneQ_isIso_iff_tests g).mpr (tests i j u g sq hi)

include sq hi in
lemma image_isIso {D : Type uH} [Category.{vH} D] (L : SSet.{v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map g) :=
  AnodyneHomotopy.map_isIso_of_anodyneQ_isIso L hL g (localized_isIso i j u g sq hi)

end SerrePositivity.SimplicialModel.KanMonoPushoutEquivalence
