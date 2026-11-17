module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Currying

/-!
概要：関手的source frameの全Hom単体を一つの要素圏にし、同じ両端と射を記録する。
方針：既存のresolutionHomを二度uncurryし、既存の要素圏の射の等式を使う。
規約：IS-W2 R03dの元の構成の全係数表示と合成則。frameや射を選び直さない。
使われ方：元の全source frameの射を、同じ両端が変数の屋根比較へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

/-- 同じ始域・標的・単体次数の全Hom係数。 -/
def sourceFrameArrowCoefficients :
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ) ⥤ Type v :=
  Functor.uncurry.obj (Functor.uncurry.obj (resolutionHom Q R))

/-- 元の全射の同じ要素圏。 -/
abbrev SourceFrameArrowElements := (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowCoefficients Q R).Elements

/-- 元の全パラメーターへの射影。 -/
def sourceFrameArrowParameters : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceFrameArrowElements Q R ⥤
    ((Cᵒᵖ × C) × SimplexCategoryᵒᵖ) :=
  Functor.Elements.π (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowCoefficients Q R)

/-- 各Hom単体の始域を反変に記録する同じ関手。 -/
def sourceFrameArrowDomain : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceFrameArrowElements Q R ⥤ Cᵒᵖ :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowParameters Q R ⋙
    ((CategoryTheory.Prod.fst (Cᵒᵖ × C) SimplexCategoryᵒᵖ ⋙ CategoryTheory.Prod.fst Cᵒᵖ C).prod'
      (CategoryTheory.Prod.snd (Cᵒᵖ × C) SimplexCategoryᵒᵖ)) ⋙
    (prodOpEquiv C (D := SimplexCategory)).inverse ⋙ (Functor.uncurry.obj Q).op

/-- 各Hom単体の標的を共変に記録する同じ関手。 -/
def sourceFrameArrowCodomain : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceFrameArrowElements Q R ⥤ C :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowParameters Q R ⋙ CategoryTheory.Prod.fst (Cᵒᵖ × C) SimplexCategoryᵒᵖ ⋙
    CategoryTheory.Prod.snd Cᵒᵖ C ⋙ R

/-- 各要素の係数は、元の両端を持つ同じ実際の射。 -/
def sourceFrameArrowValue (s : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceFrameArrowElements Q R) :
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowDomain Q R).obj s).unop ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowCodomain Q R).obj s :=
  s.val

/-- 要素圏の任意の射は、元の射の同じ反変・共変の可換四角形を与える。 -/
theorem sourceFrameArrowValue_naturality {s t : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceFrameArrowElements Q R} (f : s ⟶ t) :
    ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowDomain Q R).map f).unop ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowValue Q R s ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowCodomain Q R).map f = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowValue Q R t := by
  change ((Q.map f.hom.1.1.unop).app t.obj.2.unop ≫
      (Q.obj s.obj.1.1.unop).map f.hom.2.unop) ≫ (s.val ≫ R.map f.hom.1.2) = t.val
  have hn := (Q.map f.hom.1.1.unop).naturality f.hom.2.unop
  have hv := f.map_val
  change (Q.obj t.obj.1.1.unop).map f.hom.2.unop ≫
    (((Q.map f.hom.1.1.unop).app s.obj.2.unop ≫ s.val) ≫ R.map f.hom.1.2) = t.val at hv
  rw [← hn]
  simpa only [Category.assoc] using hv

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
