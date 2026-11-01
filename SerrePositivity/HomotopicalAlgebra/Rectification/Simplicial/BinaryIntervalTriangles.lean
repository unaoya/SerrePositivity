module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleDegeneracy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyBinarySquare

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BinaryIntervalEndpoints

/-!
# 中断した任意モデル源への一般化：BinaryIntervalTriangles

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The two actual triangles in a binary homotopy square。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0350][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0350
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The two actual triangles in a binary homotopy square

The comparison edge runs one specified interval while the other is
fixed at its first endpoint. The cone edges are the simultaneous
interval and the other interval with one input fixed at its last
endpoint. All maps are explicit; no Kan filling is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BinaryIntervalTriangles
open ComparisonTriangleDegeneracy KanComparisonTriangle
variable {T A B K : SSet.{v}} {f₀ f₁ : T ⟶ A} {g₀ g₁ : T ⟶ B}
  (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (k : A ⊗ B ⟶ K)

abbrev lowerFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  lift (T ◁ SSet.stdSimplex.σ (1 : Fin 2) ≫ F.h)
    (T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ G.h) ≫ k

abbrev upperFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  lift (T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ F.h)
    (T ◁ SSet.stdSimplex.σ (1 : Fin 2) ≫ G.h) ≫ k

lemma lower_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ lowerFamily F G k =
    (firstFixed G k (f₁ := f₁)).h := by
  rw [lowerFamily, ← Category.assoc, comp_lift, collapse_end_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    face_collapse_zero (0 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

lemma lower_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ lowerFamily F G k =
    (HomotopyBinarySquare.simultaneous F G k).h := by
  rw [lowerFamily, ← Category.assoc, comp_lift]
  have h₀ := face_collapse_zero.{v} (1 : Fin 2)
  have h₁ := face_collapse_one.{v} (0 : Fin 2)
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ at h₀
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ at h₁
  simp only [← Category.assoc, ← whiskerLeft_comp, h₀, h₁, whiskerLeft_id, Category.id_comp]
  rfl

lemma lower_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ lowerFamily F G k =
    lift F.h (fst T HomotopyBinarySquare.interval ≫ g₀) ≫ k := by
  rw [lowerFamily, ← Category.assoc, comp_lift, collapse_start_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ from
    face_collapse_one (1 : Fin 2), whiskerLeft_id, Category.id_comp]

lemma upper_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ upperFamily F G k =
    (secondFixed F k (g₁ := g₁)).h := by
  rw [upperFamily, ← Category.assoc, comp_lift, collapse_end_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    face_collapse_zero (0 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

lemma upper_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ upperFamily F G k =
    (HomotopyBinarySquare.simultaneous F G k).h := by
  rw [upperFamily, ← Category.assoc, comp_lift]
  have h₀ := face_collapse_zero.{v} (1 : Fin 2)
  have h₁ := face_collapse_one.{v} (0 : Fin 2)
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ at h₀
  change SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ at h₁
  simp only [← Category.assoc, ← whiskerLeft_comp, h₀, h₁, whiskerLeft_id, Category.id_comp]
  rfl

lemma upper_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ upperFamily F G k =
    lift (fst T HomotopyBinarySquare.interval ≫ f₀) G.h ≫ k := by
  rw [upperFamily, ← Category.assoc, comp_lift, collapse_start_interval, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ from
    face_collapse_one (1 : Fin 2), whiskerLeft_id, Category.id_comp]

def lower : Data (HomotopyBinarySquare.simultaneous F G k) (firstFixed G k (f₁ := f₁)) where
  triangle := curry (lowerFamily F G k)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, lower_zero]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, lower_one]

def upper : Data (HomotopyBinarySquare.simultaneous F G k) (secondFixed F k (g₁ := g₁)) where
  triangle := curry (upperFamily F G k)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, upper_zero]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, upper_one]

lemma lower_comparison : (comparison _ _ (lower F G k)).h =
    lift F.h (fst T HomotopyBinarySquare.interval ≫ g₀) ≫ k := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ curry (lowerFamily F G k)) = _
  rw [uncurry_natural_left, uncurry_curry, lower_two]

lemma upper_comparison : (comparison _ _ (upper F G k)).h =
    lift (fst T HomotopyBinarySquare.interval ≫ f₀) G.h ≫ k := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ curry (upperFamily F G k)) = _
  rw [uncurry_natural_left, uncurry_curry, upper_two]

end SerrePositivity.SimplicialModel.BinaryIntervalTriangles
