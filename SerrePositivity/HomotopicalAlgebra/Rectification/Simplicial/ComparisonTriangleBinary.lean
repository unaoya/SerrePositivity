module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTriangle
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyBinarySquare

/-!
# 中断した任意モデル源への一般化：ComparisonTriangleBinary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Compose a specified triangle with a specified interval。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0366][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0366
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Compose a specified triangle with a specified interval

The interval runs from its first endpoint on the comparison edge to its
second endpoint at the cone vertex. Both original cone edges are retained
under simultaneous binary composition. No Kan hypothesis is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonTriangleBinary
open KanComparisonTriangle

private lemma zero_collapse (i : Fin 2) :
    SSet.stdSimplex.δ.{v} i.castSucc ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ = 𝟙 _
  rw [← SSet.stdSimplex.map_comp]
  have hi : SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 _ := by
    fin_cases i <;> decide
  rw [hi, CategoryTheory.Functor.map_id]


private lemma collapse_edge {T B : SSet.{v}} {h₀ h₁ : T ⟶ B} (H : SSet.Homotopy h₀ h₁) :
    T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ H.h =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ h₀ := by
  have h : SSet.stdSimplex.δ.{v} (2 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) =
      SSet.stdSimplex.σ (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
    change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
      SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
    rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
    exact congrArg SSet.stdSimplex.map (by decide)
  rw [← Category.assoc, ← whiskerLeft_comp, h, whiskerLeft_comp, Category.assoc]
  have hzero : T ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst T _ ≫ SSet.ι₀ := by
    rw [SSet.stdSimplex.δ_one_eq_const]
    rfl
  rw [hzero, Category.assoc, H.h₀, ← Category.assoc]
  have hf : T ◁ SSet.stdSimplex.σ (0 : Fin 1) ≫ fst T _ = fst T _ := rfl
  rw [hf]

variable {T A B K : SSet.{v}} {f g z : T ⟶ A} {h₀ h₁ : T ⟶ B}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h₀ h₁)
  (k : A ⊗ B ⟶ K) (d : Data F G)

abbrev rightFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  lift (family F G d) (T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ H.h) ≫ k

lemma rightFamily_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ rightFamily F G H k d =
    (HomotopyBinarySquare.simultaneous G H k).h := by
  rw [rightFamily, ← Category.assoc, comp_lift, family_zero, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    zero_collapse (0 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

lemma rightFamily_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ rightFamily F G H k d =
    (HomotopyBinarySquare.simultaneous F H k).h := by
  rw [rightFamily, ← Category.assoc, comp_lift, family_one, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    zero_collapse (1 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

def right : Data (HomotopyBinarySquare.simultaneous F H k)
    (HomotopyBinarySquare.simultaneous G H k) where
  triangle := curry (rightFamily F G H k d)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, rightFamily_zero]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, rightFamily_one]


lemma right_comparison :
    (comparison _ _ (right F G H k d)).h =
      lift (comparison F G d).h (fst T HomotopyBinarySquare.interval ≫ h₀) ≫ k := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ curry (rightFamily F G H k d)) = _
  rw [uncurry_natural_left, uncurry_curry, rightFamily, ← Category.assoc, comp_lift,
    family_two, collapse_edge]

variable {f₀ f₁ : T ⟶ A} {g' h' z' : T ⟶ B}
  (L : SSet.Homotopy f₀ f₁) (M : SSet.Homotopy g' z') (N : SSet.Homotopy h' z')
  (e : Data M N)

abbrev leftFamily : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  lift (T ◁ SSet.stdSimplex.σ (0 : Fin 2) ≫ L.h) (family M N e) ≫ k

lemma leftFamily_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ leftFamily k L M N e =
    (HomotopyBinarySquare.simultaneous L N k).h := by
  rw [leftFamily, ← Category.assoc, comp_lift, family_zero, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (0 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    zero_collapse (0 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

lemma leftFamily_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ leftFamily k L M N e =
    (HomotopyBinarySquare.simultaneous L M k).h := by
  rw [leftFamily, ← Category.assoc, comp_lift, family_one, ← Category.assoc,
    ← whiskerLeft_comp]
  rw [show SSet.stdSimplex.δ.{v} (1 : Fin 3) ≫ SSet.stdSimplex.σ (0 : Fin 2) = 𝟙 _ from
    zero_collapse (1 : Fin 2), whiskerLeft_id, Category.id_comp]
  rfl

def left : Data (HomotopyBinarySquare.simultaneous L M k)
    (HomotopyBinarySquare.simultaneous L N k) where
  triangle := curry (leftFamily k L M N e)
  face_zero := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, leftFamily_zero]
  face_one := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_curry, leftFamily_one]

lemma left_comparison :
    (comparison _ _ (left k L M N e)).h =
      lift (fst T HomotopyBinarySquare.interval ≫ f₀) (comparison M N e).h ≫ k := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ curry (leftFamily k L M N e)) = _
  rw [uncurry_natural_left, uncurry_curry, leftFamily, ← Category.assoc, comp_lift,
    family_two, collapse_edge]

/-- Retain the actual triangle while changing only proved expressions for its two edges. -/
def changeEdges {T K : SSet.{v}} {f g z f' g' z' : T ⟶ K}
    {F : SSet.Homotopy f z} {G : SSet.Homotopy g z}
    {F' : SSet.Homotopy f' z'} {G' : SSet.Homotopy g' z'}
    (d : Data F G) (hF : F.h = F'.h) (hG : G.h = G'.h) : Data F' G' where
  triangle := d.triangle
  face_zero := d.face_zero.trans (congrArg curry hG)
  face_one := d.face_one.trans (congrArg curry hF)

lemma changeEdges_comparison {T K : SSet.{v}} {f g z f' g' z' : T ⟶ K}
    {F : SSet.Homotopy f z} {G : SSet.Homotopy g z}
    {F' : SSet.Homotopy f' z'} {G' : SSet.Homotopy g' z'}
    (d : Data F G) (hF : F.h = F'.h) (hG : G.h = G'.h) :
    (comparison F' G' (changeEdges d hF hG)).h = (comparison F G d).h := rfl

end SerrePositivity.SimplicialModel.ComparisonTriangleBinary
