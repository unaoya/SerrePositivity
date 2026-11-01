module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFixedColumnFactorization

/-!
# 全行の切断を同じ生成矢で表示した元の図式

概要：元の hammock の全行と全縦射を、一つの固定生成矢で切った列の圏へ持ち上げる。
方針：基準行の切断の Total 矢に各行を整列し、元の全射をそのまま使う。
規約：忘却後は元の全行・全縦射の関手に厳密に一致する。
使われ方：接頭列と残りの図式の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

def rowGenerator : Quiver.Total C :=
  let P := rowFirstCut W τ i h 0
  ⟨P.source, P.target, P.arrow⟩

def fixedRowCut (k : Fin (n.unop.len + 1)) :
    FixedCut W (rowGenerator W τ i h) ((τ.obj k).arrow i) :=
  FixedCut.ofFirstCut W (rowFirstCut W τ i h k)
    (column_firstCut_row W τ k i (rowFirstCut W τ i h 0) (rowFirstCut W τ i h k)).1.symm

def rowCutDiagram : Fin (n.unop.len + 1) ⥤
    ColumnCut W w X Y i (rowGenerator W τ i h) where
  obj k := ⟨τ.obj k, fixedRowCut W τ i h k⟩
  map f := τ.map f
  map_id k := τ.map_id k
  map_comp f g := τ.map_comp f g

lemma rowCutDiagram_forget : rowCutDiagram W τ i h ⋙
    ColumnCut.forget W w X Y i (rowGenerator W τ i h) = τ := by
  apply CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro j k f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
