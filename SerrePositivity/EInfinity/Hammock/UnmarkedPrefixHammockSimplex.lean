module

public import SerrePositivity.EInfinity.Hammock.UnmarkedSelectedPrefixSimplex
public import SerrePositivity.EInfinity.Hammock.UnmarkedPrefixHammock
public import SerrePositivity.EInfinity.Hammock.MarkedZigzagTransport

/-!
# 元の指定 prefix の実際の W-hammock と全単体作用素

概要：元の指定部分圏へ持ち上げた prefix の単体を全単体作用素へ照合する。
方針：同じ最初の列と生成矢を回収し、元の全関手の異種等式を持ち上げる。
規約：端点・語の表示を含む元の全行・全縦射の異種等式である。
使われ方：hammock の自由積分解の最初の指定因子。
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
lemma rowGenerator_index_eq : rowGenerator W τ i hi = rowGenerator W τ j hj := by
  cases hij
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ []) (θ : n ⟶ m)
  (hθ : ∃ j, column W (((graph W.paths w X Y).map θ τ).obj 0) j ≠ [])

lemma generator_simplex :
    rowGenerator W ((graph W.paths w X Y).map θ τ)
      (index W ((graph W.paths w X Y).map θ τ) hθ) (nonempty W _ hθ) =
      rowGenerator W τ (index W τ h) (nonempty W τ h) :=
  (Attachments.rowGenerator_index_eq W ((graph W.paths w X Y).map θ τ)
    (index_simplex W τ h θ hθ) (nonempty W _ hθ)
    (simplexColumn_ne_nil W τ (index W τ h) (nonempty W τ h) θ)).trans
      (rowGenerator_simplex W τ (index W τ h) (nonempty W τ h) θ
        (simplexColumn_ne_nil W τ (index W τ h) (nonempty W τ h) θ))

lemma prefixWord_simplex :
    Word.append (Word.ColumnSplit.before w (index W ((graph W.paths w X Y).map θ τ) hθ))
      (Word.single .forward) =
        Word.append (Word.ColumnSplit.before w (index W τ h)) (Word.single .forward) :=
  congrArg (fun j => Word.append (Word.ColumnSplit.before w j) (Word.single .forward))
    (index_simplex W τ h θ hθ)

lemma functor_simplex :
    HEq (functor W ((graph W.paths w X Y).map θ τ) hθ)
      (rowIndex θ ⋙ functor W τ h) :=
  Zigzag.MovingDiagram.fixedFunctor_heq (prefixWord_simplex W τ h θ hθ) rfl
    (congrArg (fun a : Quiver.Total C => (show Paths C from a.left)) (generator_simplex W τ h θ hθ))
    (diagram W ((graph W.paths w X Y).map θ τ) hθ)
    ((diagram W τ h).precomp (rowIndex θ)) (diagram_simplex W τ h θ hθ)

lemma markedFunctor_simplex :
    HEq (markedFunctor W ((graph W.paths w X Y).map θ τ) hθ)
      (rowIndex θ ⋙ markedFunctor W τ h) :=
  MarkedZigzag.liftFunctor_heq W.paths (prefixWord_simplex W τ h θ hθ) rfl
    (congrArg (fun a : Quiver.Total C => (show Paths C from a.left)) (generator_simplex W τ h θ hθ))
    (functor W ((graph W.paths w X Y).map θ τ) hθ) (rowIndex θ ⋙ functor W τ h)
    (arrow_mem W _ hθ) (fun d j => arrow_mem W τ h ((rowIndex θ).obj d) j)
    (functor_simplex W τ h θ hθ)

lemma markedSimplex_simplex :
    HEq (markedSimplex W ((graph W.paths w X Y).map θ τ) hθ)
      ((graph (⊤ : MorphismProperty (WideSubcategory W.paths))
        (Word.append (Word.ColumnSplit.before w (index W τ h)) (Word.single .forward))
        (⟨X⟩ : WideSubcategory W.paths)
        (⟨(rowGenerator W τ (index W τ h) (nonempty W τ h)).left⟩ :
          WideSubcategory W.paths)).map θ (markedSimplex W τ h)) :=
  markedFunctor_simplex W τ h θ hθ

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
