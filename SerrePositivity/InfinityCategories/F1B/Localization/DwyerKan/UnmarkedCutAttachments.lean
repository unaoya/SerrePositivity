module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitJoints
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramOfFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedRowFactorization
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzagDiagram

/-!
# 内部の固定切断と前後の全語の接続射

概要：前後の接合点を元の列の端点へ照合し、指定接頭射と残りの射を接続する。
方針：forward 列の両端の評価関手の等式と元の自然な因子化を使う。
規約：元の全縦射と接頭射の指定性を保持する。
使われ方：元の指定 prefix と残りの hammock の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

def beforeDiagram := Zigzag.MovingDiagram.ColumnSplit.before i (Zigzag.MovingDiagram.ofFunctor τ)

def afterDiagram := Zigzag.MovingDiagram.ColumnSplit.after i (Zigzag.MovingDiagram.ofFunctor τ)

def sourceJoint :=
  Zigzag.MovingDiagram.ColumnSplit.sourceJoint i (Zigzag.MovingDiagram.ofFunctor τ)

def targetJoint :=
  Zigzag.MovingDiagram.ColumnSplit.targetJoint i (Zigzag.MovingDiagram.ofFunctor τ)

include h in
lemma column_forward : w.direction i = .forward :=
  column_firstCut_forward W (τ.obj 0) i (columnFirstCut W (τ.obj 0) i h)

lemma sourceJoint_eq_rowSource : sourceJoint W τ i = rowSource W τ i h := by
  rw [rowSource_eq]
  have hi : w.source i = i.castSucc := by simp [Word.source, column_forward W τ i h]
  rw [hi]
  exact Zigzag.MovingDiagram.ColumnSplit.sourceJoint_eq i (Zigzag.MovingDiagram.ofFunctor τ)

lemma targetJoint_eq_rowTarget : targetJoint W τ i = rowTarget W τ i h := by
  rw [rowTarget_eq]
  have hi : w.target i = i.succ := by simp [Word.target, column_forward W τ i h]
  rw [hi]
  exact Zigzag.MovingDiagram.ColumnSplit.targetJoint_eq i (Zigzag.MovingDiagram.ofFunctor τ)

def leftAttachment : sourceJoint W τ i ⟶
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from (rowGenerator W τ i h).left) :=
  eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ rowPrefix W τ i h

def rightAttachment :
    (Functor.const (Fin (n.unop.len + 1))).obj (show Paths C from (rowGenerator W τ i h).right) ⟶
      targetJoint W τ i :=
  rowResidual W τ i h ≫ eqToHom (targetJoint_eq_rowTarget W τ i h).symm

lemma attachment_factorization :
    leftAttachment W τ i h ≫ rowGeneratorMap W τ i h ≫ rightAttachment W τ i h =
      eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ rowColumn W τ i h ≫
        eqToHom (targetJoint_eq_rowTarget W τ i h).symm := by
  dsimp only [leftAttachment, rightAttachment]
  simpa only [Category.assoc] using congrArg
    (fun f => eqToHom (sourceJoint_eq_rowSource W τ i h) ≫ f ≫
      eqToHom (targetJoint_eq_rowTarget W τ i h).symm) (rowColumn_factorization W τ i h)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
