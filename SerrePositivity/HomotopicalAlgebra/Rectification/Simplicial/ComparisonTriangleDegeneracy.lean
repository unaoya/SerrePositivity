module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTetrahedron

/-!
# 中断した任意モデル源への一般化：ComparisonTriangleDegeneracy

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Degenerate comparison triangles and a fixed-edge round-trip coherence。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0368][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0368
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Degenerate comparison triangles and a fixed-edge round-trip coherence

The diagonal of the cone on one selected interval is a degenerate
comparison, with the actual constant interval at its starting map.
Together with two oppositely directed selected comparison triangles,
it bounds a tetrahedron retaining both original whole triangles.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonTriangleDegeneracy
open KanComparisonTriangle

lemma face_collapse_zero (i : Fin 2) :
    SSet.stdSimplex.δ.{v} i.castSucc ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ = 𝟙 _
  rw [← SSet.stdSimplex.map_comp]
  have hi : SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 _ := by
    fin_cases i <;> decide
  rw [hi, CategoryTheory.Functor.map_id]

lemma face_collapse_one (i : Fin 2) :
    SSet.stdSimplex.δ.{v} i.succ ≫ SSet.stdSimplex.σ (1 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ = 𝟙 _
  rw [← SSet.stdSimplex.map_comp]
  have hi : SimplexCategory.δ i.succ ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 _ := by
    fin_cases i <;> decide
  rw [hi, CategoryTheory.Functor.map_id]

lemma face_collapse_start :
    SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

lemma face_collapse_end :
    SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (1 : Fin 2) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (0 : Fin 2) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

variable {A B : SSet.{v}} {u₀ u₁ : A ⟶ B}

lemma collapse_start_interval (H : SSet.Homotopy u₀ u₁) :
    A ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ A ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ H.h =
      fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ u₀ := by
  rw [← Category.assoc, ← whiskerLeft_comp, face_collapse_start,
    whiskerLeft_comp, Category.assoc]
  have hzero : A ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst A _ ≫ SSet.ι₀ := by
    rw [SSet.stdSimplex.δ_one_eq_const]
    rfl
  rw [hzero, Category.assoc, H.h₀, ← Category.assoc]
  rfl

lemma collapse_end_interval (H : SSet.Homotopy u₀ u₁) :
    A ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ A ◁ SSet.stdSimplex.σ (1 : Fin 2) ≫ H.h =
      fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ u₁ := by
  rw [← Category.assoc, ← whiskerLeft_comp, face_collapse_end,
    whiskerLeft_comp, Category.assoc]
  have hone : A ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst A _ ≫ SSet.ι₁ := by
    rw [SSet.stdSimplex.δ_zero_eq_const]
    rfl
  rw [hone, Category.assoc, H.h₁, ← Category.assoc]
  rfl

variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

def diagonal : Data F F where
  triangle := SSet.stdSimplex.σ (0 : Fin 2) ≫ curry F.h
  face_zero := by
    have h : SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ :=
      face_collapse_zero (0 : Fin 2)
    rw [← Category.assoc, h, Category.id_comp]
  face_one := by
    have h : SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ :=
      face_collapse_zero (1 : Fin 2)
    rw [← Category.assoc, h, Category.id_comp]

lemma diagonal_comparison : (comparison F F (diagonal F)).h =
    fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (SSet.stdSimplex.σ (0 : Fin 2) ≫ curry F.h)) = _
  rw [← Category.assoc, face_collapse_start, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero,
    uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.point, uncurry_curry, ← Category.assoc]
  rfl

variable (a : Data F G) (b : Data G F)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

abbrev roundTrip : KanComparisonTetrahedron.Filler F G F a (diagonal F) b :=
  KanComparisonTetrahedron.build F G F a (diagonal F) b hK

abbrev family : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  KanComparisonTetrahedron.coherence F G F a (diagonal F) b (roundTrip F G a b hK)

lemma family_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ family F G a b hK =
    (comparison F G a).h := KanComparisonTetrahedron.coherence_two _ _ _ _ _ _ _

lemma family_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ family F G a b hK =
    (comparison G F b).h := KanComparisonTetrahedron.coherence_zero _ _ _ _ _ _ _

lemma family_constant : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ family F G a b hK =
    fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f := by
  rw [family, KanComparisonTetrahedron.coherence_one, diagonal_comparison]

end SerrePositivity.SimplicialModel.ComparisonTriangleDegeneracy
