module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-!
# 中断した任意モデル源への一般化：KanComparisonTriangle

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：A comparison triangle retains two selected whole interval families。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0409][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0409
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# A comparison triangle retains two selected whole interval families

Both given comparisons have the same final map. The missing edge is a
comparison of their initial maps, and the two original edges are fixed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

structure Data where
  triangle : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom T).obj K
  face_zero : SSet.stdSimplex.δ (0 : Fin 3) ≫ triangle = curry G.h
  face_one : SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle = curry F.h

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def build : Data F G := by
  have hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ curry G.h =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ curry F.h :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one G).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one F).symm
  let ht := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exists_triangle (terminal.from ((ihom T).obj K))
    (SimplexParameterHom.native_kan T K hK) (curry G.h) (curry F.h)
    (terminal.from _) hc (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  exact ⟨ht.choose, ht.choose_spec.1, ht.choose_spec.2.1⟩

variable (d : Data F G)

abbrev family : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K := uncurry d.triangle

lemma family_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ family F G d = G.h := by
  rw [family, ← uncurry_natural_left, d.face_zero, uncurry_curry]

lemma family_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ family F G d = F.h := by
  rw [family, ← uncurry_natural_left, d.face_one, uncurry_curry]

private lemma vertex_zero :
    SSet.stdSimplex.δ.{v} (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

private lemma vertex_one :
    SSet.stdSimplex.δ.{v} (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

def comparison : SSet.Homotopy f g :=
  CurriedHomotopy.ofEdge (SSet.stdSimplex.δ (2 : Fin 3) ≫ d.triangle)
    (by rw [← Category.assoc, vertex_zero, Category.assoc, d.face_one]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero F)
    (by rw [← Category.assoc, vertex_one, Category.assoc, d.face_zero]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_zero G)

lemma family_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ family F G d =
    (comparison F G d).h := by
  change _ = uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ d.triangle)
  rw [uncurry_natural_left]

end SerrePositivity.SimplicialModel.KanComparisonTriangle
