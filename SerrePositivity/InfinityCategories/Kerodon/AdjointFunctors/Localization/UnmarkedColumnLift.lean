module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumn
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowCutDiagram

/-!
# 固定切断の圏への元の図式の一意な持ち上げ

概要：任意の添字圏の元の図式とその切断を、全射を保つ持ち上げへ束ねる。
方針：固定切断の一意性により選択の違いを消し、前合成を厳密に保持する。
規約：自然性は入力にせず元の全射を使う。忘却後は元の関手に一致する。
使われ方：全行の再添字と単体作用素への整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uI vI uJ vJ
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
  (X Y : Paths C) (i : Fin w.length) (a : Quiver.Total C)

lemma object_ext (P Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) (h : P.row = Q.row) : P = Q := by
  rcases P with ⟨P, p⟩
  rcases Q with ⟨Q, q⟩
  dsimp only at h
  cases h
  have he : p = q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedCut_ext W p q
  cases he
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift (object_ext)


variable {I : Type uI} [Category.{vI} I]

def lift (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y)
    (P : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a ((F.obj j).arrow i)) : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a where
  obj j := ⟨F.obj j, P j⟩
  map f := F.map f
  map_id j := F.map_id j
  map_comp f g := F.map_comp f g

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift (lift)


lemma lift_forget (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y)
    (P : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a ((F.obj j).arrow i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift.lift W w X Y i a F P ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.forget W w X Y i a = F := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift (lift_forget)


lemma lift_ext (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y)
    (P Q : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a ((F.obj j).arrow i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift.lift W w X Y i a F P = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift.lift W w X Y i a F Q := by
  have h : P = Q := funext (fun j => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedCut_ext W (P j) (Q j))
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift (lift_ext)


lemma lift_precomp {J : Type uJ} [Category.{vJ} J] (K : J ⥤ I)
    (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) (P : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a ((F.obj j).arrow i)) :
    lift W w X Y i a (K ⋙ F) (fun j => P (K.obj j)) = K ⋙ lift W w X Y i a F P := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift (lift_precomp)


lemma rowCutDiagram_eq_lift {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift.lift W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h) τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ i h) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift (rowCutDiagram_eq_lift)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnLift
