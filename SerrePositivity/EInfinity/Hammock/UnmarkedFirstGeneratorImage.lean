module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstGeneratorWordAction
public import SerrePositivity.EInfinity.Hammock.UnmarkedRowCutDiagram
public import SerrePositivity.EInfinity.Hammock.Diagram

/-!
# 元の全語の図式で選んだ最初の生成矢の回収

概要：最小列の像の等式と元の生成矢の一致を、実際の各単体の選択へ接続する。
方針：同じ列の切断の一意性により列の番号の表示を移す。
規約：元の WordAction と元の nerve の全行の図式を使う。
使われ方：prefix と残りを元の全語の hammock 余極限へ降ろす。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C}

lemma column_cut_generator_index {w : Word} (S : Zigzag W.paths w X Y)
    {i j : Fin w.length} (hij : i = j) (P : FirstCut W (S.arrow i))
    (Q : FirstCut W (S.arrow j)) :
    (⟨P.source, P.target, P.arrow⟩ : Quiver.Total C) = ⟨Q.source, Q.target, Q.arrow⟩ := by
  cases hij
  exact congrArg (fun R : FirstCut W (S.arrow i) =>
    (⟨R.source, R.target, R.arrow⟩ : Quiver.Total C)) (firstCut_ext W P Q)

lemma firstColumn_generator_wordAction (f : a ⟶ b) (S : Zigzag W.paths a X Y)
    (hS : ∃ i, column W S i ≠ []) (hT : ∃ j, column W (WordAction.obj f S) j ≠ [])
    (P : FirstCut W (S.arrow (firstColumn W S hS)))
    (Q : FirstCut W ((WordAction.obj f S).arrow (firstColumn W (WordAction.obj f S) hT))) :
    (⟨Q.source, Q.target, Q.arrow⟩ : Quiver.Total C) = ⟨P.source, P.target, P.arrow⟩ := by
  let R := columnFirstCut W (WordAction.obj f S) (f.orderHom (firstColumn W S hS))
    (column_wordAction_nonempty W f S _ (firstColumn_nonempty W S hS))
  exact (column_cut_generator_index W (WordAction.obj f S)
    (firstColumn_wordAction W f S hS hT) Q R).trans (firstFiber_generator W f S hS P R)

lemma rowGenerator_wordAction (f : a ⟶ b) {n : SimplexCategoryᵒᵖ}
    (τ : (graph W.paths a X Y).obj n) (hS : ∃ i, column W (τ.obj 0) i ≠ [])
    (hT : ∃ j, column W ((((graphDiagram W.paths X Y).map f).app n τ).obj 0) j ≠ []) :
    rowGenerator W (((graphDiagram W.paths X Y).map f).app n τ)
      (firstColumn W ((((graphDiagram W.paths X Y).map f).app n τ).obj 0) hT)
      (firstColumn_nonempty W _ hT) =
    rowGenerator W τ (firstColumn W (τ.obj 0) hS) (firstColumn_nonempty W _ hS) :=
  firstColumn_generator_wordAction W f (τ.obj 0) hS hT _ _

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
