module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTriangle
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# 中断した任意モデル源への一般化：ComparisonTriangleHorn

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The specified two comparison edges glue to their actual outer horn。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0369][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0369
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The specified two comparison edges glue to their actual outer horn
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

abbrev hornFaces : ∀ (j : Fin 3) (_ : j ≠ 2),
    SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ (ihom T).obj K :=
  fun j _ => if j = 0 then curry G.h else curry F.h

lemma hornCompatible : SSet.horn.IsCompatible (hornFaces F G) := by
  intro j k hj hk hjk
  fin_cases j <;> fin_cases k <;> first
  | exact (hj rfl).elim
  | exact (hk rfl).elim
  | exact ((not_lt_of_ge (by decide)) hjk).elim
  | exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one G).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edge_one F).symm

abbrev hornMap : (SSet.horn.{v} 2 2).toSSet ⟶ (ihom T).obj K := (hornCompatible F G).desc

lemma hornMap_zero : SSet.horn.ι (2 : Fin 3) 0 (by decide) ≫ hornMap F G = curry G.h :=
  (hornCompatible F G).ι_desc 0 (by decide)

lemma hornMap_one : SSet.horn.ι (2 : Fin 3) 1 (by decide) ≫ hornMap F G = curry F.h :=
  (hornCompatible F G).ι_desc 1 (by decide)

lemma Data.horn_restriction (d : Data F G) : (SSet.horn 2 2).ι ≫ d.triangle = hornMap F G := by
  apply SSet.horn.hom_ext'
  intro j hj
  rw [← Category.assoc, SSet.horn.ι_ι]
  fin_cases j
  · exact d.face_zero.trans (hornMap_zero F G).symm
  · exact d.face_one.trans (hornMap_one F G).symm
  · exact (hj rfl).elim

end SerrePositivity.SimplicialModel.KanComparisonTriangle
