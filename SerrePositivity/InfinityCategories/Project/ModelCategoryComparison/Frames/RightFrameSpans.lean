module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SpecialHammock
public import Mathlib.CategoryTheory.Elements

/-!
概要：元の right frame Hom の全単体から特殊な三本矢へ実関手を作る。
方針：恒等左脚と同じ right frame augmentation を持つ三本矢に送る。
規約：全単体・全作用素・元の射を保ち、弱同値性は後続で扱う。
使われ方：一般モデル圏の right frame と hammock の共通比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory Limits HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：元の right frame の全 augmentation は自明 cofibration。
方針：反対圏の同じ Reedy 自明 fibration の各成分を読む。
規約：元の標的に fibrancy を要求しない。使われ方：三本矢の右脚の条件。 -/
lemma rightFrameUnit_trivialCofibration (Y : C) (n : SimplexCategoryᵒᵖ) :
    trivialCofibrations C (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).app n) := by
  have h := trivialFibration_app simplex (r.augmentation.app (op Y)) (r.trivial (op Y)) n.unop
  rw [trivialFibrations_op] at h
  exact h

/-- 概要：元の Hom の単体から同じ特殊な三本矢を作る。
方針：左脚を恒等射、右脚を元の augmentation、中間射を単体自身とする。
規約：元の対象と実際の射を保持。使われ方：全単体の比較関手の対象写像。 -/
def rightFrameElementSpan (X Y : C) (s : ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y).Elements) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y where
  left := X
  right := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r).obj Y).obj s.obj
  leftMap := 𝟙 X
  rightMap := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).app s.obj
  middle := s.val
  left_mem := (trivialFibrations C).id_mem _
  right_mem := rightFrameUnit_trivialCofibration r Y s.obj

/-- 概要：元の right frame Hom の全単体と全作用素を三本矢へ送る。
方針：作用素は同じ right frame 射と左の恒等射に送る。
規約：反対化による単体の変更を行わない。使われ方：hammock への実比較。 -/
def rightFrameElementSpanFunctor (X Y : C) :
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y).Elements ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y where
  obj := rightFrameElementSpan r X Y
  map {s t} f := {
    left := 𝟙 X
    right := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r).obj Y).map f.hom
    left_w := Category.id_comp _
    middle_w := by
      change s.val ≫ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r).obj Y).map f.hom = 𝟙 X ≫ t.val
      exact f.map_val.trans (Category.id_comp _).symm
    right_w := by
      have h := ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).naturality f.hom
      exact h.symm.trans (Category.id_comp _) }
  map_id s := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · rfl
    · exact ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r).obj Y).map_id s.obj
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact (Category.id_comp _).symm
    · exact ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameDiagram r).obj Y).map_comp f.hom g.hom

/-- 概要：元の射から作った零単体の中間射は元の augmentation 合成。
方針：単体の埋め込みと三本矢の定義を読む。
規約：局所化前の実射の等式。使われ方：元の局所化射への正規化。 -/
lemma rightFrameElementSpan_unit_middle (X Y : C) (n : SimplexCategoryᵒᵖ) (f : X ⟶ Y) :
    (rightFrameElementSpan r X Y (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y).elementsMk n
      ((((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHomUnit r X).app Y).app n) f))).middle =
        f ≫ ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameUnit r).app Y).app n := rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
