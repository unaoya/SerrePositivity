module

public import SerrePositivity.EInfinity.Hammock.ColimitCompositionPoints
public import SerrePositivity.EInfinity.Hammock.UnmarkedValueAppend
public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyImage

/-!
# 元の hammock の合成と元の非指定文字列評価

概要：元の余極限の合成は非指定文字列の順序付き連結へ評価される。
方針：各次数の元の標準射の共同全射性と元の全列の連結則を使う。
規約：元の composePoint・colimitValue・生成射の標準射を保持する。
使われ方：任意の三因子の貼り戻しの非空性と因子回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y Z : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma colimitValue_composePoint (p : (colimitGraph W.paths X Y).obj n)
    (q : (colimitGraph W.paths Y Z).obj n) :
    (colimitValue W X Z).app n (composePoint W.paths X Y Z p q) =
      List.append ((colimitValue W X Y).app n p) ((colimitValue W Y Z).app n q) := by
  obtain ⟨a, σ, rfl⟩ := colimit_point_surjective (graphDiagram W.paths X Y) n p
  obtain ⟨b, τ, rfl⟩ := colimit_point_surjective (graphDiagram W.paths Y Z) n q
  have hc := composePoint_inclusions W.paths X Y Z a b σ τ
  have hv := FirstFactor.colimitValue_inclusion W X Z (Word.append a b)
    (σ.prod' τ ⋙ ZigzagAppend.functor)
  have hp := FirstFactor.colimitValue_inclusion W X Y a σ
  have hq := FirstFactor.colimitValue_inclusion W Y Z b τ
  exact (congrArg ((colimitValue W X Z).app n) hc).trans
    (hv.trans ((value_append W (σ.obj 0) (τ.obj 0)).trans (congrArg₂ List.append hp.symm hq.symm)))

lemma colimitValue_arrowPoint {A B : Paths C} (p : A ⟶ B) :
    (colimitValue W A B).app n (arrowPoint W.paths p n) =
      SimplicialLocalization.GeneratorWord.erase W p :=
  (FirstFactor.colimitValue_inclusion W A B (Word.single .forward)
    (arrowSimplex W.paths p n)).trans (value_forward W p)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
