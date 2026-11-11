module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Permutation
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# テンソル単位の隣接交換

## 概要
HA 3.2.4.7 の零入力への代入で、単位と同型な係数の隣接交換が恒等となることを使う。

## 方針
単位同士の組紐を単位子で縮約し、テンソル冪の隣接交換の自然性で同型に沿って移す。

## 規約
対称モノイダル圏の既存のテンソル冪と隣接交換をそのまま使う。

## 使われ方
消去する色の入力の置換に対する係数射の不変性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory BraidedCategory
open SerrePositivity.TensorPowers
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- テンソル単位の冪の各隣接交換は恒等射。 -/
lemma tensorUnit_adjacent_hom (n : ℕ) (i : Fin n) :
    (adjacentIso (𝟙_ C) n i).hom = 𝟙 _ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (swapFirstIso (𝟙_ C) n).hom = _
      simp [swapFirstIso, power]
    · change (𝟙_ C) ◁ (adjacentIso (𝟙_ C) n j).hom = _
      rw [ih]
      simp only [whiskerLeft_id]
      rfl

/-- テンソル単位と同型な対象の冪でも、各隣接交換は恒等射。 -/
lemma adjacent_hom_eq_id_of_isoUnit {X : C} (e : X ≅ 𝟙_ C) (n : ℕ) (i : Fin n) :
    (adjacentIso X n i).hom = 𝟙 _ := by
  have : IsIso (map e.hom (n + 1)) :=
    show IsIso ((powerFunctor (n + 1)).map e.hom) from inferInstance
  apply (cancel_mono (map e.hom (n + 1))).mp
  simpa only [tensorUnit_adjacent_hom, Category.comp_id, Category.id_comp] using
    (adjacentIso_naturality e.hom n i).symm

end SerrePositivity.EInfinity
