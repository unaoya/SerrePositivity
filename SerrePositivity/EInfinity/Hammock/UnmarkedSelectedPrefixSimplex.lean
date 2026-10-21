module

public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedDiagramsSimplex
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstColumnSimplex
public import SerrePositivity.EInfinity.Hammock.UnmarkedAttachedPrefix

/-!
# 選んだ最初の非指定列の prefix・残りと全単体作用素

概要：基準行から選んだ最小列の位置と全図式の異種等式を結合する。
方針：位置の等式で表示を移し、同じ固定列での元の再添字の整合を使う。
規約：位置・生成矢の表示・元の全縦射を保持する。
使われ方：指定 prefix の hammock 単体の単体的整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) {i j : Fin w.length} (hij : i = j)
  (hi : column W (τ.obj 0) i ≠ []) (hj : column W (τ.obj 0) j ≠ [])

include hij in
lemma prefixDiagram_index_heq : HEq (prefixDiagram W τ i hi) (prefixDiagram W τ j hj) := by
  cases hij
  rfl

include hij in
lemma residualDiagram_index_heq : HEq (residualDiagram W τ i hi) (residualDiagram W τ j hj) := by
  cases hij
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ []) (θ : n ⟶ m)
  (hθ : ∃ j, column W (((graph W.paths w X Y).map θ τ).obj 0) j ≠ [])

lemma index_simplex : index W ((graph W.paths w X Y).map θ τ) hθ = index W τ h :=
  firstColumn_simplex W τ h θ hθ

lemma diagram_simplex :
    HEq (diagram W ((graph W.paths w X Y).map θ τ) hθ)
      ((diagram W τ h).precomp (rowIndex θ)) :=
  (Attachments.prefixDiagram_index_heq W ((graph W.paths w X Y).map θ τ)
    (index_simplex W τ h θ hθ) (nonempty W _ hθ)
    (simplexColumn_ne_nil W τ (index W τ h) (nonempty W τ h) θ)).trans
      (Attachments.prefixDiagram_simplex W τ (index W τ h) (nonempty W τ h) θ
        (simplexColumn_ne_nil W τ (index W τ h) (nonempty W τ h) θ))

lemma residual_simplex :
    HEq (Attachments.residualDiagram W ((graph W.paths w X Y).map θ τ)
      (index W ((graph W.paths w X Y).map θ τ) hθ) (nonempty W _ hθ))
      ((Attachments.residualDiagram W τ (index W τ h) (nonempty W τ h)).precomp (rowIndex θ)) :=
  (Attachments.residualDiagram_index_heq W ((graph W.paths w X Y).map θ τ)
    (index_simplex W τ h θ hθ) (nonempty W _ hθ)
    (simplexColumn_ne_nil W τ (index W τ h) (nonempty W τ h) θ)).trans
      (Attachments.residualDiagram_simplex W τ (index W τ h) (nonempty W τ h) θ
        (simplexColumn_ne_nil W τ (index W τ h) (nonempty W τ h) θ))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
