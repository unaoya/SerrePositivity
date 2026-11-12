module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.PiZeroConstant
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection
public import Mathlib.Tactic.CrossRefAttribute

/-!
# anodyne局所化で可逆な射は実際の連結成分の全単射を誘導する

## 概要
anodyne局所化で可逆な射は実際の連結成分の全単射を誘導する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間のπ₀、局所化後の射、ホモトピー類の計算に利用できる。
[棚卸し m0513][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0513
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Anodyne-localized equivalences induce bijections on actual components

Discrete Kan tests identify precomposition on homotopy classes with
precomposition on functions out of components. No model structure is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.PiZeroLocalization

variable {X Y : SSet.{v}} {T : Type v}

@[kerodon 00GQ]
def classEquiv : HomotopyClasses.obj X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T) ≃ (SSet.π₀ X → T) where
  toFun := Quot.lift _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents (fun _ _ ⟨H⟩ => congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homotopy_eq H))
  invFun t := HomotopyClasses.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.fromComponents t)
  left_inv z := by
    refine Quot.inductionOn z (fun f => ?_)
    exact congrArg HomotopyClasses.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv.left_inv f)
  right_inv t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.homEquiv.right_inv t

lemma classEquiv_pre (f : X ⟶ Y) (z : HomotopyClasses.obj Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete T)) :
    classEquiv (HomotopyClasses.pre f z) = classEquiv z ∘ SSet.mapπ₀ f := by
  refine Quot.inductionOn z (fun g => ?_)
  funext c
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  rfl

lemma precomposition_bijective (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (T : Type v) :
    Function.Bijective (fun t : SSet.π₀ Y → T => t ∘ SSet.mapπ₀ f) := by
  let eX := classEquiv (X := X) (T := T)
  let eY := classEquiv (X := Y) (T := T)
  have he : (fun t : SSet.π₀ Y → T => t ∘ SSet.mapπ₀ f) =
      fun t => eX (HomotopyClasses.pre f (eY.symm t)) := by
    funext t
    rw [classEquiv_pre]
    exact congrArg (· ∘ SSet.mapπ₀ f) (eY.apply_symm_apply t).symm
  rw [he]
  exact eX.bijective.comp
    ((KanTestDetection.tests_of_anodyneQ_isIso f hf _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.discrete_terminal_rlp T)).comp
      eY.symm.bijective)

lemma bijective_of_precomposition {A B : Type v} (p : A → B)
    (hs : Function.Surjective (fun t : B → A => t ∘ p))
    (hi : Function.Injective (fun t : B → B => t ∘ p)) : Function.Bijective p := by
  obtain ⟨l, hl⟩ := hs id
  have hr : p ∘ l = id := hi (by
    funext a
    exact congrArg p (congrFun hl a))
  refine ⟨fun a b hab => ?_, fun b => ⟨l b, congrFun hr b⟩⟩
  calc
    a = l (p a) := (congrFun hl a).symm
    _ = l (p b) := congrArg l hab
    _ = b := congrFun hl b

/-- anodyne局所化で可逆な射は実際の連結成分の全単射を誘導する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
実写像または区間ホモトピーの関係を商へ降ろす。
代表元に依らないことを確認してから、誘導写像と比較を組み立てる。
-/
lemma piZero_bijective (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    Function.Bijective (SSet.mapπ₀ f) :=
  bijective_of_precomposition _
    (precomposition_bijective f hf (SSet.π₀ X)).surjective
    (precomposition_bijective f hf (SSet.π₀ Y)).injective

lemma inverts_anodyne : SSet.anodyneExtensions.IsInvertedBy SSet.π₀Functor.{v} := by
  intro X Y f hf
  exact (CategoryTheory.isIso_iff_bijective _).mpr
    (piZero_bijective f (Localization.inverts AnodyneHomotopy.anodyneQ _ f hf))

end SerrePositivity.SimplicialModel.PiZeroLocalization
