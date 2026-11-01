module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedCutGeneratorTransport

/-!
# 単体作用素による基準行の変更と同じ生成矢

概要：元の任意の単体作用素で全行を制限しても、最初の非指定生成矢は同じである。
方針：元の全行の非指定文字列の不変性と切断の Total 矢の一意性を使う。
規約：全単体作用素と元の nerve の写像を使う。
使われ方：切断図式の単体作用素への厳密な自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)

include h in
lemma simplexColumn_ne_nil : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ [] := by
  change column W (τ.obj (θ.unop.toOrderHom 0)) i ≠ []
  rw [column_row W τ _ i]
  exact h

lemma rowGenerator_simplex
    (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ []) :
    rowGenerator W ((graph W.paths w X Y).map θ τ) i hθ = rowGenerator W τ i h :=
  (column_firstCut_row W τ (θ.unop.toOrderHom 0) i
    (rowFirstCut W τ i h 0) (rowFirstCut W ((graph W.paths w X Y).map θ τ) i hθ 0)).1.symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
