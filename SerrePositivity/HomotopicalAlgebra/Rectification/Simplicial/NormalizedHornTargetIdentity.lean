module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetComposition

/-!
# 中断した任意モデル源への一般化：NormalizedHornTargetIdentity

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The previously selected identity comparison bounds a relative constant-edge triangle。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0504][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0504
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The previously selected identity comparison bounds a relative constant-edge triangle
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.NormalizedHornTargetIdentity
open NormalizedHornTargetComparison
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def loop : SSet.Homotopy (NormalizedHornFilling.section_ K i hK)
    (NormalizedHornFilling.section_ K i hK) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints (comparison i hK hK (𝟙 K))
    (by dsimp only [sourceThenMap]; rw [CategoryTheory.Functor.map_id, Category.comp_id])
    (by dsimp only [mapThenTarget]; rw [CategoryTheory.Functor.map_id, Category.id_comp])

lemma loop_h : (loop K i hK).h = (comparison i hK hK (𝟙 K)).h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h _ _ _

abbrev constant := KanActualHomotopy.refl (NormalizedHornFilling.section_ K i hK)

lemma constant_h : (constant K i hK).h =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      NormalizedHornFilling.section_ K i hK := rfl

def triangle : (ihom (SSet.horn (n + 1) i).toSSet).obj K ⊗
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K :=
  RelativeComparisonTriangle.triangle (loop K i hK) (constant K i hK) (constant K i hK)
    (KanHornFamilyLifting.restriction K i) (KanHornFamilyLifting.all_mono_rlp K i hK)
    (inputs (K := K) i).ι ((inputs (K := K) i).ι ≫ NormalizedHornFilling.section_ K i hK)
    (𝟙 _) (by rw [Category.assoc, NormalizedHornFilling.section_restriction])
    (by
      rw [loop_h, comparison_horn]
      dsimp only [sourceThenMap]
      rw [CategoryTheory.Functor.map_id, Category.comp_id,
        NormalizedHornFilling.section_restriction])
    (by rw [constant_h, Category.assoc, NormalizedHornFilling.section_restriction])
    (by rw [constant_h, Category.assoc, NormalizedHornFilling.section_restriction])
    (by
      rw [loop_h, comparison_inputs]
      dsimp only [sourceThenMap]
      rw [CategoryTheory.Functor.map_id, Category.comp_id])
    (by rw [constant_h, whiskerRight_fst_assoc])
    (by rw [constant_h, whiskerRight_fst_assoc])

lemma triangle_face (k : Fin 3) : _ ◁ SSet.stdSimplex.δ k ≫ triangle K i hK =
    ![(constant K i hK).h, (constant K i hK).h, (loop K i hK).h] k :=
  RelativeComparisonTriangle.triangle_face _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k

lemma triangle_base : triangle K i hK ≫ KanHornFamilyLifting.restriction K i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) := by
  exact (RelativeComparisonTriangle.triangle_base _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans
    (Category.comp_id _)

lemma triangle_relative : (inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ triangle K i hK =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫
      (inputs (K := K) i).ι ≫ NormalizedHornFilling.section_ K i hK :=
  RelativeComparisonTriangle.triangle_relative _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable {T : SSet.{v}} (t : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

abbrev family := t ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ triangle K i hK

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    family K i hK (j ≫ t) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ family K i hK t := by
  dsimp only [family]
  rw [comp_whiskerRight, Category.assoc]

lemma family_original : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ family K i hK t =
    t ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (comparison i hK hK (𝟙 K)).h := by
  dsimp only [family]
  rw [whisker_exchange_assoc, triangle_face]
  change _ ≫ (loop K i hK).h = _
  rw [loop_h]

abbrev evaluation := uncurry (family K i hK t)

lemma evaluation_reindex {U : SSet.{v}} (j : U ⟶ T) :
    evaluation K i hK (j ≫ t) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁
        (j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ evaluation K i hK t := by
  dsimp only [evaluation]
  rw [family_reindex, uncurry_natural_left]

end SerrePositivity.SimplicialModel.NormalizedHornTargetIdentity
