module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramOfFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowFactorization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiagram

/-!
# 内部の固定切断と前後の全語の接続射

概要：前後の接合点を元の列の端点へ照合し、指定接頭射と残りの射を接続する。
方針：forward 列の両端の評価関手の等式と元の自然な因子化を使う。
規約：元の全縦射と接頭射の指定性を保持する。
使われ方：元の指定 prefix と残りの hammock の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])

def beforeDiagram := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.before i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

def afterDiagram := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitDiagram.after i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

def sourceJoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints.sourceJoint i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

def targetJoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints.targetJoint i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

include h in
lemma column_forward : w.direction i = .forward :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_firstCut_forward W (τ.obj 0) i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnFirstCut W (τ.obj 0) i h)

lemma sourceJoint_eq_rowSource : sourceJoint W τ i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowSource W τ i h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowSource_eq]
  have hi : w.source i = i.castSucc := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.column_forward W τ i h]
  rw [hi]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints.sourceJoint_eq i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

lemma targetJoint_eq_rowTarget : targetJoint W τ i = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowTarget W τ i h := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowTarget_eq]
  have hi : w.target i = i.succ := by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.column_forward W τ i h]
  rw [hi]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnSplitJoints.targetJoint_eq i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ)

def leftAttachment : sourceJoint W τ i ⟶
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).left) :=
  eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i h

def rightAttachment :
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h).right) ⟶
      targetJoint W τ i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W τ i h ≫ eqToHom (targetJoint_eq_rowTarget W τ i h).symm

lemma attachment_factorization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment W τ i h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ i h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment W τ i h =
      eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn W τ i h ≫
        eqToHom (targetJoint_eq_rowTarget W τ i h).symm := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.leftAttachment, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.rightAttachment]
  simpa only [Category.assoc] using congrArg
    (fun f => eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ f ≫
      eqToHom (targetJoint_eq_rowTarget W τ i h).symm) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn_factorization W τ i h)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments
