module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonTetrahedron
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonTriangle

/-!
# 中断した任意モデル源への一般化：NormalizedComparisonSquare

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A chosen comparison disc strictly natural in the whole source parameter。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0495][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0495
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A chosen comparison disc strictly natural in the whole source parameter

The common diagonal and both tetrahedra are chosen using the normalized
operations in K. Reindexing all four prescribed cone triangles therefore
commutes strictly with both entire three-dimensional fillers and both
remaining comparison triangles.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedComparisonSquare
open KanComparisonTriangle
variable {T K : SSet.{v}} {f₀ f₁ f₂ f₃ z : T ⟶ K}
  (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
  (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)
  (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def build : KanComparisonSquare.Filler F₀ F₁ F₂ F₃ a b c d where
  diagonal := NormalizedComparisonTriangle.build F₀ F₂ hK
  left := NormalizedComparisonTetrahedron.build F₀ F₁ F₂ a
    (NormalizedComparisonTriangle.build F₀ F₂ hK) b hK
  right := NormalizedComparisonTetrahedron.build F₀ F₃ F₂ c
    (NormalizedComparisonTriangle.build F₀ F₂ hK) d hK

abbrev left : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  KanComparisonSquare.left F₀ F₁ F₂ F₃ a b c d (build F₀ F₁ F₂ F₃ a b c d hK)

abbrev right : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K :=
  KanComparisonSquare.right F₀ F₁ F₂ F₃ a b c d (build F₀ F₁ F₂ F₃ a b c d hK)

lemma left_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ left F₀ F₁ F₂ F₃ a b c d hK =
    (comparison F₀ F₁ a).h := KanComparisonSquare.left_first _ _ _ _ _ _ _ _ _

lemma left_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ left F₀ F₁ F₂ F₃ a b c d hK =
    (comparison F₁ F₂ b).h := KanComparisonSquare.left_second _ _ _ _ _ _ _ _ _

lemma right_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ right F₀ F₁ F₂ F₃ a b c d hK =
    (comparison F₀ F₃ c).h := KanComparisonSquare.right_first _ _ _ _ _ _ _ _ _

lemma right_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ right F₀ F₁ F₂ F₃ a b c d hK =
    (comparison F₃ F₂ d).h := KanComparisonSquare.right_second _ _ _ _ _ _ _ _ _

lemma common_diagonal : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ left F₀ F₁ F₂ F₃ a b c d hK =
    T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ right F₀ F₁ F₂ F₃ a b c d hK :=
  KanComparisonSquare.common_diagonal _ _ _ _ _ _ _ _ _

variable {U : SSet.{v}} (i : U ⟶ T)
local notation "G₀" => HomotopyClasses.preHomotopy i F₀
local notation "G₁" => HomotopyClasses.preHomotopy i F₁
local notation "G₂" => HomotopyClasses.preHomotopy i F₂
local notation "G₃" => HomotopyClasses.preHomotopy i F₃
local notation "ta" => ComparisonCoherenceRestriction.triangle i F₀ F₁ a
local notation "tb" => ComparisonCoherenceRestriction.triangle i F₁ F₂ b
local notation "tc" => ComparisonCoherenceRestriction.triangle i F₀ F₃ c
local notation "td" => ComparisonCoherenceRestriction.triangle i F₃ F₂ d

private lemma triangle_ext {V P : SSet.{v}} {f g z : V ⟶ P}
    {F : SSet.Homotopy f z} {G : SSet.Homotopy g z}
    (a b : Data F G) (h : a.triangle = b.triangle) : a = b := by
  cases a
  cases b
  cases h
  rfl

private lemma diagonal_reindex :
    ComparisonCoherenceRestriction.triangle i F₀ F₂ (NormalizedComparisonTriangle.build F₀ F₂ hK) =
      NormalizedComparisonTriangle.build G₀ G₂ hK := by
  apply triangle_ext
  exact (NormalizedComparisonTriangle.triangle_reindex F₀ F₂ hK i).symm

lemma left_tetrahedron_reindex : (build G₀ G₁ G₂ G₃ ta tb tc td hK).left.tetrahedron =
    (build F₀ F₁ F₂ F₃ a b c d hK).left.tetrahedron ≫ (pre i).app K := by
  change NormalizedComparisonTetrahedron.tetrahedron G₀ G₁ G₂ ta
    (NormalizedComparisonTriangle.build G₀ G₂ hK) tb hK = _
  rw [← diagonal_reindex]
  exact NormalizedComparisonTetrahedron.tetrahedron_reindex F₀ F₁ F₂ a
    (NormalizedComparisonTriangle.build F₀ F₂ hK) b hK i

lemma right_tetrahedron_reindex : (build G₀ G₁ G₂ G₃ ta tb tc td hK).right.tetrahedron =
    (build F₀ F₁ F₂ F₃ a b c d hK).right.tetrahedron ≫ (pre i).app K := by
  change NormalizedComparisonTetrahedron.tetrahedron G₀ G₃ G₂ tc
    (NormalizedComparisonTriangle.build G₀ G₂ hK) td hK = _
  rw [← diagonal_reindex]
  exact NormalizedComparisonTetrahedron.tetrahedron_reindex F₀ F₃ F₂ c
    (NormalizedComparisonTriangle.build F₀ F₂ hK) d hK i

lemma left_reindex : left G₀ G₁ G₂ G₃ ta tb tc td hK =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ left F₀ F₁ F₂ F₃ a b c d hK := by
  change uncurry (SSet.stdSimplex.δ (3 : Fin 4) ≫
    (build G₀ G₁ G₂ G₃ ta tb tc td hK).left.tetrahedron) = _
  rw [left_tetrahedron_reindex, ← Category.assoc]
  exact uncurry_pre_app K
    (SSet.stdSimplex.δ (3 : Fin 4) ≫ (build F₀ F₁ F₂ F₃ a b c d hK).left.tetrahedron) i

lemma right_reindex : right G₀ G₁ G₂ G₃ ta tb tc td hK =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ right F₀ F₁ F₂ F₃ a b c d hK := by
  change uncurry (SSet.stdSimplex.δ (3 : Fin 4) ≫
    (build G₀ G₁ G₂ G₃ ta tb tc td hK).right.tetrahedron) = _
  rw [right_tetrahedron_reindex, ← Category.assoc]
  exact uncurry_pre_app K
    (SSet.stdSimplex.δ (3 : Fin 4) ≫ (build F₀ F₁ F₂ F₃ a b c d hK).right.tetrahedron) i

end SerrePositivity.SimplicialModel.NormalizedComparisonSquare
