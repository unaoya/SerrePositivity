module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.ArrowSpan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom
public import Mathlib.CategoryTheory.Elements

/-!
# Frame Hom の全単体を三本矢へ送る図式

概要：Dwyer–Kan §7 の共通比較に、元の cosimplicial Hom の全単体を送る。
方針：各単体を同じ augmentation と右脚を持つ三本矢にし、全作用素を元の frame の射で送る。
規約：元の Hom の全単体と全作用素を保持し、モデル構造は要求しない。
使われ方：特殊な hammock の nerve と元の Map^h の高次比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

open _root_.CategoryTheory _root_.Opposite

variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C)
  {X Y Z : C} (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, L (p.app n)) (j : Y ⟶ Z) (hj : R j)

/-- 概要：元の frame Hom の一つの単体を同じ三本矢へ送る（Dwyer–Kan §7）。
方針：同じ次数の frame 対象と実際の単体の射を使う。
規約：両脚と元の中間射を変更しない。
使われ方：全単体の比較図式の対象。 -/
def frameElementSpan (s : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y where
  left := A.obj s.unop.obj.unop
  right := Z
  leftMap := p.app s.unop.obj.unop
  middle := s.unop.val
  rightMap := j
  left_mem := hp _
  right_mem := hj

/-- 概要：全単体作用素を元の三本矢の間の射へ送る（Dwyer–Kan §7）。
方針：単体の元の frame の射と終域の恒等射を使う。
規約：単体作用素の射と中間射の整合を明示する。
使われ方：同じ frame Hom の全次数の比較。 -/
def frameElementSpanMap {s t : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ} (f : s ⟶ t) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpan L R A p hp j hj s ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpan L R A p hp j hj t where
  left := A.map f.unop.hom.unop
  right := 𝟙 Z
  left_w := by
    have h := p.naturality f.unop.hom.unop
    change A.map f.unop.hom.unop ≫ p.app t.unop.obj.unop =
      p.app s.unop.obj.unop ≫ 𝟙 X at h
    exact h.trans (Category.comp_id _)
  middle_w := by
    change s.unop.val ≫ 𝟙 Z = A.map f.unop.hom.unop ≫ t.unop.val
    exact (Category.comp_id _).trans f.unop.map_val.symm
  right_w := Category.comp_id _

/-- 概要：元の frame Hom の全単体から三本矢への関手（Dwyer–Kan §7）。
方針：対象と全作用素の同じ比較を元の frame の関手則で束ねる。
規約：要素圏の反対を使い、cosimplicial な射の向きを保持する。
使われ方：特殊な hammock の nerve との共通比較の図式。 -/
def frameElementSpanFunctor : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y
    where
  obj := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpan L R A p hp j hj
  map := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameElementSpanMap L R A p hp j hj
  map_id s := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact A.map_id _
    · rfl
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact A.map_comp f.unop.hom.unop g.unop.hom.unop
    · exact (Category.id_comp _).symm

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
