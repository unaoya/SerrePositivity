module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowCutDiagram

/-!
# 元の全行の列の自然な因子化図式

概要：元の全行の列を、指定接頭列・固定生成矢・残りの自然変換へ分解する。
方針：元の全行を持ち上げた関手に、固定列の自然な因子化を制限する。
規約：元の全縦射の成分を保持し、元の列の図式への回収式を証明する。
使われ方：元の hammock の行を切断して貼り戻す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

def rowSource : Fin (n.unop.len + 1) ⥤ Paths C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.sourceEvaluation W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)

def rowTarget : Fin (n.unop.len + 1) ⥤ Paths C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut.targetEvaluation W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)

def rowPrefix : rowSource W τ i h ⟶
    (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).left) where
  app k := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ i h k).left
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumnFactorization.prefixMap W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)).naturality
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h).map f)

def rowResidual :
    (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).right) ⟶ rowTarget W τ i h where
  app k := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ i h k).right
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumnFactorization.residualMap W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)).naturality
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h).map f)

def rowGeneratorMap :
    (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).left) ⟶
    (Functor.const (Fin (n.unop.len + 1))).obj
      (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).right) :=
  (Functor.const (Fin (n.unop.len + 1))).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).hom.toPath

def rowColumn : rowSource W τ i h ⟶ rowTarget W τ i h where
  app k := (τ.obj k).arrow i
  naturality _ _ f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedColumnFactorization.columnMap W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)).naturality
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h).map f)

lemma rowPrefix_mem (k : Fin (n.unop.len + 1)) : W.paths ((rowPrefix W τ i h).app k) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ i h k).left_mem

lemma rowColumn_factorization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ i h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W τ i h = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn W τ i h := by
  apply NatTrans.ext
  funext k
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ i h k).factorization.symm

lemma rowSource_eq : rowSource W τ i h = τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (w.source i) :=
  congrArg (fun F : Fin (n.unop.len + 1) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y =>
    F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (w.source i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram_forget W τ i h)

lemma rowTarget_eq : rowTarget W τ i h = τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (w.target i) :=
  congrArg (fun F : Fin (n.unop.len + 1) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y =>
    F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (w.target i)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram_forget W τ i h)

lemma rowSource_map_mem {j k : Fin (n.unop.len + 1)} (f : j ⟶ k) :
    W.paths ((rowSource W τ i h).map f) := (τ.map f).app_mem (w.source i)

lemma rowTarget_map_mem {j k : Fin (n.unop.len + 1)} (f : j ⟶ k) :
    W.paths ((rowTarget W τ i h).map f) := (τ.map f).app_mem (w.target i)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
