module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CostructuredArrowDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.CostructuredArrowCofinality
public import Mathlib.CategoryTheory.Grothendieck

/-!
# 固定右脚の比較を右変数の全図式に自然に束ねる

概要：Low 命題 3.7 の分解側の比較を全右対象の自然変換と全図式の関手へ束ねる。
方針：元の costructured arrow の前合成と後合成の厳密な可換性を使う。
規約：全対象・全射の自然性を証明し、全図式の余終性は別途扱う。
使われ方：元の三本矢の全図式への成分ごとの余終性の適用。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

open CategoryTheory
open _root_.SerrePositivity.InfinityCategories

variable {K L C J : Type u} [Category.{u} K] [Category.{u} L]
  [Category.{u} C] [Category.{u} J]

/-- 概要：固定右対象の元の比較は右変数に自然（Low 命題 3.7）。
方針：元の前合成と右対象への後合成の全対象・全射での交換を使う。
規約：自然変換の各成分は同じ CostructuredArrow.pre。
使われ方：右脚の全図式の比較。 -/
def costructuredArrowDiagramPre (P : K ⥤ L) (Q : L ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram (P ⋙ Q) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram Q where
  app V := (CostructuredArrow.pre P Q V).toCatHom
  naturality _ _ _ := rfl

/-- 概要：元の全図式の比較の各成分は left cofinal（Low 命題 3.7）。
方針：元の同じ成分の right fibration に沿う底変換を使う。
規約：終域への全係数射を含む自然変換の各成分。
使われ方：全図式の成分ごとの余終性の入力。 -/
lemma costructuredArrowDiagramPre_isLeftCofinal (P : K ⥤ L) (Q : L ⥤ C)
    (hP : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap P)) (V : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap ((costructuredArrowDiagramPre P Q).app V).toFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.costructuredArrowPre_isLeftCofinal P Q V hP

/-- 概要：元の右変数の全図式への比較関手（Low 命題 3.7）。
方針：全係数射に自然な元の比較を同じ Grothendieck 構成で送る。
規約：成分ごとの余終性から全体の余終性を無証明で推論しない。
使われ方：三本矢の元の全図式への比較の適用先。 -/
def fixedRightGrothendieckComparison (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C) :
    Grothendieck (R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram (P ⋙ Q)) ⥤
      Grothendieck (R ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram Q) :=
  Grothendieck.map (Functor.whiskerLeft R (costructuredArrowDiagramPre P Q))

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
