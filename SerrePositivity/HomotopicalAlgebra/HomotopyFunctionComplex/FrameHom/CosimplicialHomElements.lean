module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# 元の cosimplicial Hom の反対要素圏と comma 圏

概要：同じ Hom の全単体と作用素を、元の cosimplicial 図式の comma 圏で表示する。
方針：単体の次数・元の射・元の単体作用素を取り出す明示的な順逆を作る。
規約：モデル構造・置換・cofibrancy は不要。反対を fiber の要素圏だけに取る。
使われ方：固定右脚の元の Hom と全右脚の分解の図式の接続。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.Opposite

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements


variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) (V : C)

/-- 元の Hom の単体を同じ次数と元の射の comma 対象へ送る。 -/
def toComma : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ ⥤ CostructuredArrow A V where
  obj s := CostructuredArrow.mk (Y := s.unop.obj.unop) s.unop.val
  map f := CostructuredArrow.homMk f.unop.hom.unop f.unop.map_val
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の comma 対象と作用素から同じ Hom の単体と作用素を復元。 -/
def fromComma : CostructuredArrow A V ⥤ (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ where
  obj s := op (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).elementsMk (op s.left) s.hom)
  map f := (Functor.Elements.homMk f.left.op (CostructuredArrow.w f)).op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の Hom の全単体と作用素は順逆で厳密に戻る。 -/
lemma toComma_fromComma : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.toComma A V ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.fromComma A V = 𝟭 _ := rfl

/-- 元の comma の全対象と作用素も順逆で厳密に戻る。 -/
lemma fromComma_toComma : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.fromComma A V ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.toComma A V = 𝟭 _ := rfl

/-- 元の全単体の反対要素圏と同じ cosimplicial 図式の comma 圏の明示的な同値。 -/
def equivalence : (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ ≌ CostructuredArrow A V :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.toComma A V) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.fromComma A V)
    (eqToIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.toComma_fromComma A V).symm) (eqToIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.fromComma_toComma A V))

/-- 右対象の元の射への後合成と同じ順関手は全対象・全射で厳密に可換。 -/
lemma toComma_naturality {V W : C} (f : V ⟶ W) :
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f).mapElements.op ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.toComma A W =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.toComma A V ⋙ CostructuredArrow.map f := rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements
