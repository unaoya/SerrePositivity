module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFixedColumn
public import SerrePositivity.EInfinity.Hammock.UnmarkedRowCutDiagram

/-!
# 固定切断の圏への元の図式の一意な持ち上げ

概要：任意の添字圏の元の図式とその切断を、全射を保つ持ち上げへ束ねる。
方針：固定切断の一意性により選択の違いを消し、前合成を厳密に保持する。
規約：自然性は入力にせず元の全射を使う。忘却後は元の関手に一致する。
使われ方：全行の再添字と単体作用素への整合。
-/

@[expose] public section
universe u v uI vI uJ vJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : Word)
  (X Y : Paths C) (i : Fin w.length) (a : Quiver.Total C)

lemma object_ext (P Q : ColumnCut W w X Y i a) (h : P.row = Q.row) : P = Q := by
  rcases P with ⟨P, p⟩
  rcases Q with ⟨Q, q⟩
  dsimp only at h
  cases h
  have he : p = q := fixedCut_ext W p q
  cases he
  rfl

variable {I : Type uI} [Category.{vI} I]

def lift (F : I ⥤ Zigzag W.paths w X Y)
    (P : ∀ j, FixedCut W a ((F.obj j).arrow i)) : I ⥤ ColumnCut W w X Y i a where
  obj j := ⟨F.obj j, P j⟩
  map f := F.map f
  map_id j := F.map_id j
  map_comp f g := F.map_comp f g

lemma lift_forget (F : I ⥤ Zigzag W.paths w X Y)
    (P : ∀ j, FixedCut W a ((F.obj j).arrow i)) :
    lift W w X Y i a F P ⋙ forget W w X Y i a = F := rfl

lemma lift_ext (F : I ⥤ Zigzag W.paths w X Y)
    (P Q : ∀ j, FixedCut W a ((F.obj j).arrow i)) :
    lift W w X Y i a F P = lift W w X Y i a F Q := by
  have h : P = Q := funext (fun j => fixedCut_ext W (P j) (Q j))
  cases h
  rfl

lemma lift_precomp {J : Type uJ} [Category.{vJ} J] (K : J ⥤ I)
    (F : I ⥤ Zigzag W.paths w X Y) (P : ∀ j, FixedCut W a ((F.obj j).arrow i)) :
    lift W w X Y i a (K ⋙ F) (fun j => P (K.obj j)) = K ⋙ lift W w X Y i a F P := rfl

lemma rowCutDiagram_eq_lift {n : SimplexCategoryᵒᵖ} (τ : (graph W.paths w X Y).obj n)
    (h : column W (τ.obj 0) i ≠ []) :
    rowCutDiagram W τ i h = lift W w X Y i (rowGenerator W τ i h) τ (fixedRowCut W τ i h) := rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
