module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryObjects
/-!
# 先頭 backward の元の指定列への後合成

概要：指定射による始点の後合成を元の全頂点・全列で構成する。
方針：始点の成分だけを恒等射とし、残りの元の全射と可換正方形を保持する。
規約：元の指定条件・両端条件と全射列の関手則を保持する。
使われ方：DK9.3・10.3・5.7の元の固定語の端点 variance。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {w : Word} {X X' Y : C}
def backwardArrow (S : Zigzag W (Word.cons .backward w) X Y) (f : X ⟶ X') :
    ∀ i, vertex S X' ((Word.cons .backward w).source i) ⟶
      vertex S X' ((Word.cons .backward w).target i) :=
  Fin.cases (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) (tailArrow S X')

variable [W.IsMultiplicative]
def backward (S : Zigzag W (Word.cons .backward w) X Y) (f : X ⟶ X') (hf : W f) :
    Zigzag W (Word.cons .backward w) X' Y where
  vertex := vertex S X'
  first := rfl
  last := S.last
  arrow := backwardArrow S f
  backward_mem i hi := by
    cases i using Fin.cases with
    | zero =>
      change W (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f)
      have hS : W (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first) := by
        simpa only [eqToHom_refl, Category.id_comp] using
          (Direction.transport_mem rfl S.first (S.arrow (0 : Fin (w.length + 1)))).mpr
            (S.backward_mem (0 : Fin (w.length + 1)) rfl)
      simpa only [Category.assoc] using
        W.comp_mem (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first) f hS hf
    | succ i =>
      change W (tailArrow S X' i)
      exact (Direction.transport_mem _ _ _).2 (S.backward_mem i.succ hi)
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
