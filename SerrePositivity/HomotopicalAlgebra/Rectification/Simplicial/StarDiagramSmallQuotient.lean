module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallDiagramQuotient
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.SmallSubdiagramObstruction

/-!
# 中断した任意モデル源への一般化：StarDiagramSmallQuotient

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The congruence construction smallifies the large star by a natural quotient。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0579][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0579
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The congruence construction smallifies the large star by a natural quotient

The earlier obstruction ruled out every small natural source. Here all
quotient size and finite-boundary certificates are proved for the opposite
direction, without a model structure in either value universe.
-/

@[expose] public section
universe v uH vH
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.StarDiagramSmallQuotient
open SmallSubdiagramObstruction

abbrev original : Index (Type v) ⥤ SSet.{v + 1} := diagram (Type v)
abbrev relation : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.Congruence original.{v} := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.total original

lemma small (d : Index (Type v)) (n : SimplexCategoryᵒᵖ) :
    Small.{v} (Quotient (relation.rel d n)) := by
  exact SmallDiagramQuotient.total_small.{v, v + 1} (F := original) d n

lemma boundary (d : Index (Type v)) :
    SSet.modelCategoryQuillen.I.rlp ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.DiagramQuotient.projection relation).app d) := by
  apply SmallDiagramQuotient.total_boundary_rlp original d
  cases d with
  | of d =>
    change (MorphismProperty.monomorphisms SSet.{v + 1}).rlp
      (terminal.from point)
    have := isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ terminalIsTerminal
      (terminal.from point)
    exact (MorphismProperty.monomorphisms _).rlp.of_isIso _
  | star => exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.terminal_mono_rlp PUnit

/-- The actual small strict diagram is the quotient construction, not a chosen constant model. -/
abbrev functor : Index (Type v) ⥤ SSet.{v} :=
  SmallDiagramQuotient.functor.{v, v + 1} relation small

abbrev projection : original.{v} ⟶ functor ⋙ SSet.uliftFunctor.{v + 1, v} :=
  SmallDiagramQuotient.projection.{v, v + 1} relation small

def imageIso {H : Type uH} [Category.{vH} H] (L : SSet.{v + 1} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    original ⋙ L ≅ (functor ⋙ SSet.uliftFunctor.{v + 1, v}) ⋙ L :=
  SmallDiagramQuotient.imageIso.{v, v + 1} relation small boundary L hL

lemma kan (d : Index (Type v)) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (functor.obj d)) :=
  SmallDiagramQuotient.kan.{v, v + 1} relation small boundary d
    (values_kan (Type v) PUnit d)

end SerrePositivity.SimplicialModel.StarDiagramSmallQuotient
