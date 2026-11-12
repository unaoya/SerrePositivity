module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryReedyFactorization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalKanTests
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LocalizedMonoReedy
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.BoundaryReedyFactorization
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalKanTests
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.LocalizedMonoReedy

/-!
# 各行で局所化可逆な二重単体写像の対角は局所化可逆となる

## 概要
各行で局所化可逆な二重単体写像の対角は局所化可逆となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。

## 規約と注意
値宇宙のモデル構造は置かず、anodyne射を反転する局所化で可逆性を読む。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0385][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0385
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Rowwise anodyne-localized equivalences are diagonal equivalences in any value universe
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.Reedy SerrePositivity.SimplicialModel

namespace SerrePositivity.BisimplicialModel

lemma localized_diagonal_map_of_reedyMono {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hm : reedyLeft simplexOp (MorphismProperty.monomorphisms _) f)
    (hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (diagonal.map f)) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.localized_diagonal_map_of_reedy_localizedMonos f ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.reedy_iff f).mpr ⟨hm, hf⟩)

/-- 各行で局所化可逆な二重単体写像の対角は局所化可逆となる。

値宇宙のモデル構造は置かず、anodyne射を反転する局所化で可逆性を読む。
対角の右随伴と境界内部Homの比較を使い、相対matching射を計算する。
必要な持ち上げ条件またはBrownの補題を、この実際の比較へ適用する。
-/
lemma localized_diagonal_map {A B : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : A ⟶ B)
    (hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (f.app n))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (diagonal.map f)) := by
  have : MorphismProperty.IsWeakFactorizationSystem _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.{v}
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.right.{v} := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.reedy_wfs
  have : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.{v}.IsMultiplicative := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left_eq_llp]
    infer_instance
  have : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.{v}.IsStableUnderCobaseChange := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left_eq_llp]
    infer_instance
  let d := MorphismProperty.factorizationData _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.right (coprod.desc f (𝟙 B))
  let l := coprod.inl ≫ d.i
  let r := coprod.inr ≫ d.i
  have hlp : l ≫ d.p = f := by
    dsimp only [l]
    rw [Category.assoc, d.fac, coprod.inl_desc]
  have hrp : r ≫ d.p = 𝟙 B := by
    dsimp only [r]
    rw [Category.assoc, d.fac, coprod.inr_desc]
  have hlm : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left l := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.of_isPushout (IsPushout.of_hasBinaryCoproduct' A B)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.initial_left B)) d.hi
  have hrm : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left r := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.left.of_isPushout (IsPushout.of_hasBinaryCoproduct' A B).flip
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.initial_left A)) d.hi
  have hl : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (l.app n)) := by
    intro n
    have : IsIso (AnodyneHomotopy.anodyneQ.map (d.p.app n)) :=
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.right_app_localized d.p d.hp n
    have h := congrArg AnodyneHomotopy.anodyneQ.map (congr_app hlp n)
    rw [NatTrans.comp_app, Functor.map_comp] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (l.app n) ≫
        AnodyneHomotopy.anodyneQ.map (d.p.app n)) := h.symm ▸ hf n
    exact (isIso_comp_right_iff _ _).mp hc
  have hr : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map (r.app n)) := by
    intro n
    have : IsIso (AnodyneHomotopy.anodyneQ.map (d.p.app n)) :=
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.right_app_localized d.p d.hp n
    have h := congrArg AnodyneHomotopy.anodyneQ.map (congr_app hrp n)
    rw [NatTrans.comp_app, NatTrans.id_app, Functor.map_comp, CategoryTheory.Functor.map_id] at h
    have hc : IsIso (AnodyneHomotopy.anodyneQ.map (r.app n) ≫
        AnodyneHomotopy.anodyneQ.map (d.p.app n)) := h.symm ▸ inferInstanceAs (IsIso (𝟙 _))
    exact (isIso_comp_right_iff _ _).mp hc
  let Q := diagonal ⋙ AnodyneHomotopy.anodyneQ
  have : IsIso (Q.map l) := localized_diagonal_map_of_reedyMono l hlm hl
  have : IsIso (Q.map r) := localized_diagonal_map_of_reedyMono r hrm hr
  have hp : IsIso (Q.map d.p) := by
    have h := congrArg Q.map hrp
    rw [Q.map_comp, Q.map_id] at h
    have hc : IsIso (Q.map r ≫ Q.map d.p) := h.symm ▸ inferInstanceAs (IsIso (𝟙 _))
    exact (isIso_comp_left_iff _ _).mp hc
  have h := congrArg Q.map hlp
  rw [Q.map_comp] at h
  exact h ▸ inferInstanceAs (IsIso (Q.map l ≫ Q.map d.p))

end SerrePositivity.BisimplicialModel
