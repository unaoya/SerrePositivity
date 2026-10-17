module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonCoherenceTransport

/-!
# 中断した任意モデル源への一般化：ComparisonCoherenceRestriction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Parameter restriction of entire selected tetrahedra and comparison discs。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0364][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0364
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Parameter restriction of entire selected tetrahedra and comparison discs

All four original cone triangles, the common diagonal, and both whole
three-dimensional fillers are restricted together. Selected fillers at
another parameter are not silently identified with these restrictions.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonCoherenceRestriction
open KanComparisonTriangle
variable {T U K : SSet.{v}} (i : U ⟶ T)
  {f₀ f₁ f₂ f₃ z : T ⟶ K}
  (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
  (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)

abbrev triangle {f g z : T ⟶ K} (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)
    (a : Data F G) : Data (HomotopyClasses.preHomotopy i F) (HomotopyClasses.preHomotopy i G) :=
  ComparisonTriangleTransport.data F G _ _ ((pre i).app K)
    (curry_pre_app i F.h) (curry_pre_app i G.h) a

local notation "G₀" => HomotopyClasses.preHomotopy i F₀
local notation "G₁" => HomotopyClasses.preHomotopy i F₁
local notation "G₂" => HomotopyClasses.preHomotopy i F₂
local notation "G₃" => HomotopyClasses.preHomotopy i F₃

variable (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)
  (e : KanComparisonSquare.Filler F₀ F₁ F₂ F₃ a b c d)

local notation "ta" => triangle i F₀ F₁ a
local notation "tb" => triangle i F₁ F₂ b
local notation "tc" => triangle i F₀ F₃ c
local notation "td" => triangle i F₃ F₂ d

abbrev square : KanComparisonSquare.Filler G₀ G₁ G₂ G₃ ta tb tc td :=
  ComparisonCoherenceTransport.square F₀ F₁ F₂ F₃ G₀ G₁ G₂ G₃ ((pre i).app K)
    (curry_pre_app i F₀.h) (curry_pre_app i F₁.h)
    (curry_pre_app i F₂.h) (curry_pre_app i F₃.h) a b c d e

lemma left_family : KanComparisonSquare.left G₀ G₁ G₂ G₃ ta tb tc td
    (square i F₀ F₁ F₂ F₃ a b c d e) =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
        KanComparisonSquare.left F₀ F₁ F₂ F₃ a b c d e := by
  change uncurry _ = _
  rw [ComparisonCoherenceTransport.square_left_triangle]
  exact uncurry_pre_app K _ i

lemma right_family : KanComparisonSquare.right G₀ G₁ G₂ G₃ ta tb tc td
    (square i F₀ F₁ F₂ F₃ a b c d e) =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
        KanComparisonSquare.right F₀ F₁ F₂ F₃ a b c d e := by
  change uncurry _ = _
  rw [ComparisonCoherenceTransport.square_right_triangle]
  exact uncurry_pre_app K _ i

lemma left_tetrahedron_family :
    uncurry (square i F₀ F₁ F₂ F₃ a b c d e).left.tetrahedron =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ uncurry e.left.tetrahedron :=
  uncurry_pre_app K e.left.tetrahedron i

lemma right_tetrahedron_family :
    uncurry (square i F₀ F₁ F₂ F₃ a b c d e).right.tetrahedron =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ uncurry e.right.tetrahedron :=
  uncurry_pre_app K e.right.tetrahedron i

lemma diagonal_family : uncurry (square i F₀ F₁ F₂ F₃ a b c d e).diagonal.triangle =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ uncurry e.diagonal.triangle :=
  uncurry_pre_app K e.diagonal.triangle i

lemma left_tetrahedron_identity :
    (square (𝟙 T) F₀ F₁ F₂ F₃ a b c d e).left.tetrahedron = e.left.tetrahedron := by
  change e.left.tetrahedron ≫ (pre (𝟙 T)).app K = _
  rw [pre_id, NatTrans.id_app, Category.comp_id]

lemma right_tetrahedron_identity :
    (square (𝟙 T) F₀ F₁ F₂ F₃ a b c d e).right.tetrahedron = e.right.tetrahedron := by
  change e.right.tetrahedron ≫ (pre (𝟙 T)).app K = _
  rw [pre_id, NatTrans.id_app, Category.comp_id]

variable {V : SSet.{v}} (k : V ⟶ U)

lemma left_tetrahedron_comp :
    (square k G₀ G₁ G₂ G₃ ta tb tc td (square i F₀ F₁ F₂ F₃ a b c d e)).left.tetrahedron =
      (square (k ≫ i) F₀ F₁ F₂ F₃ a b c d e).left.tetrahedron := by
  change (e.left.tetrahedron ≫ (pre i).app K) ≫ (pre k).app K =
    e.left.tetrahedron ≫ (pre (k ≫ i)).app K
  have h : (pre i).app K ≫ (pre k).app K = (pre (k ≫ i)).app K :=
    RelativeChoiceSpace.restriction_comp k i
  rw [Category.assoc, h]

lemma right_tetrahedron_comp :
    (square k G₀ G₁ G₂ G₃ ta tb tc td (square i F₀ F₁ F₂ F₃ a b c d e)).right.tetrahedron =
      (square (k ≫ i) F₀ F₁ F₂ F₃ a b c d e).right.tetrahedron := by
  change (e.right.tetrahedron ≫ (pre i).app K) ≫ (pre k).app K =
    e.right.tetrahedron ≫ (pre (k ≫ i)).app K
  have h : (pre i).app K ≫ (pre k).app K = (pre (k ≫ i)).app K :=
    RelativeChoiceSpace.restriction_comp k i
  rw [Category.assoc, h]

end SerrePositivity.SimplicialModel.ComparisonCoherenceRestriction
