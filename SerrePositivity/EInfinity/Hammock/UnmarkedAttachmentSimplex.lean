module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.EInfinity.Hammock.UnmarkedRowFactorizationSimplex
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingPrecompLaws

/-!
# 元の内部接続自然変換と全単体作用素

概要：前後の接合点と内部切断を繋ぐ元の自然変換を、再添字へ照合する。
方針：語の切断の再添字と元の行の因子化の単体的整合を使う。
規約：元の接合点関手と生成矢の端点の表示を保持する。
使われ方：prefix・残りの全図式の単体的整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma beforeDiagram_simplex :
    HEq (beforeDiagram W ((graph W.paths w X Y).map θ τ) i)
      ((beforeDiagram W τ i).precomp (rowIndex θ)) :=
  ColumnSplit.before_precomp (rowIndex θ) i (ofFunctor τ)

lemma afterDiagram_simplex :
    HEq (afterDiagram W ((graph W.paths w X Y).map θ τ) i)
      ((afterDiagram W τ i).precomp (rowIndex θ)) :=
  ColumnSplit.after_precomp (rowIndex θ) i (ofFunctor τ)

lemma sourceJoint_simplex : sourceJoint W ((graph W.paths w X Y).map θ τ) i =
    rowIndex θ ⋙ sourceJoint W τ i :=
  congrArg (fun F => F.leftPart.jointFunctor)
    (ColumnSplit.expanded_precomp (rowIndex θ) i (ofFunctor τ))

lemma targetJoint_simplex : targetJoint W ((graph W.paths w X Y).map θ τ) i =
    rowIndex θ ⋙ targetJoint W τ i :=
  congrArg (fun F => F.jointFunctor)
    (ColumnSplit.expanded_precomp (rowIndex θ) i (ofFunctor τ))

lemma whiskerLeft_eqToHom {D E : Type*} [Category D] [Category E]
    (K : D ⥤ E) {A B : E ⥤ Paths C} (e : A = B) :
    Functor.whiskerLeft K (eqToHom e) = eqToHom (congrArg (fun F => K ⋙ F) e) := by
  cases e
  rfl

lemma leftAttachment_simplex :
    HEq (leftAttachment W ((graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (rowIndex θ) (leftAttachment W τ i h)) := by
  dsimp only [leftAttachment]
  rw [Functor.whiskerLeft_comp, whiskerLeft_eqToHom]
  simp only [eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
  exact rowPrefix_simplex W τ i h θ hθ

lemma rightAttachment_simplex :
    HEq (rightAttachment W ((graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (rowIndex θ) (rightAttachment W τ i h)) := by
  dsimp only [rightAttachment]
  rw [Functor.whiskerLeft_comp, whiskerLeft_eqToHom]
  simp only [comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  exact rowResidual_simplex W τ i h θ hθ

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
