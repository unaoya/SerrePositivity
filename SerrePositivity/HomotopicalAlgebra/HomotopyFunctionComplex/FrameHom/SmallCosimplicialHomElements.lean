module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 同じ宇宙の小圏に揃えた元の Hom と comma の比較

概要：元の Hom の反対要素圏と分解の comma 圏を、同じ上限の小圏で比較する。
方針：元の次数と射を up/down する明示的な順逆を作る。
規約：対象・元の射・全作用素を保持し、同値の逆の代表を選ばない。
使われ方：元の全右脚の小さい図式への fiber の不変性の適用。
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.Opposite

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements


variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) (V : C)

/-- 元の cosimplicial 図式の前後の対象・射の宇宙だけを揃える。 -/
abbrev smallDiagram : AsSmall.{max w u v} SimplexCategory ⥤ AsSmall.{max w u v} C :=
  AsSmall.down ⋙ A ⋙ AsSmall.up

/-- 元の単体の同じ次数と射を持ち上げて、小さい comma 対象に送る。 -/
def smallToComma :
    AsSmall.{max w u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ) ⥤
      CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram.{u, v, w} A) (AsSmall.up.obj V) where
  obj s := CostructuredArrow.mk
    (Y := AsSmall.up.obj (AsSmall.down.obj s).unop.obj.unop)
    (AsSmall.up.map (AsSmall.down.obj s).unop.val)
  map f := CostructuredArrow.homMk
    (AsSmall.up.map (AsSmall.down.map f).unop.hom.unop) (by
      apply ULift.ext
      exact (AsSmall.down.map f).unop.map_val)
  map_id s := by apply CostructuredArrow.hom_ext; rfl
  map_comp f g := by apply CostructuredArrow.hom_ext; rfl

/-- 同じ小さい comma 対象と作用素を down して元の全単体へ戻す。 -/
def smallFromComma :
    CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram.{u, v, w} A) (AsSmall.up.obj V) ⥤
      AsSmall.{max w u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ) where
  obj s := AsSmall.up.obj (op (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).elementsMk
    (op (AsSmall.down.obj s.left)) s.hom.down))
  map f := AsSmall.up.map ((Functor.Elements.homMk f.left.down.op (by
    exact congrArg ULift.down (CostructuredArrow.w f))).op)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 同じ全単体の宇宙を揃えた順逆は厳密に戻る。 -/
lemma smallToComma_smallFromComma :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma.{u, v, w} A V ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallFromComma A V = 𝟭 _ := rfl

/-- 同じ小さい comma の全対象・全射も厳密に戻る。 -/
lemma smallFromComma_smallToComma :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallFromComma.{u, v, w} A V ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A V = 𝟭 _ := rfl

/-- 同じ元の単体と射を保存する小圏の明示的な同値。 -/
def smallEquivalence :
    AsSmall.{max w u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ) ≌
      CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram.{u, v, w} A) (AsSmall.up.obj V) :=
  CategoryTheory.Equivalence.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A V) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallFromComma A V)
    (eqToIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma_smallFromComma A V).symm)
    (eqToIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallFromComma_smallToComma A V))

/-- 元の右対象の射で移送する、反対要素圏の同じ小さい関手。 -/
def smallElementsMap {V W : C} (f : V ⟶ W) :
    AsSmall.{max w u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj V).Elements)ᵒᵖ) ⥤
      AsSmall.{max w u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj W).Elements)ᵒᵖ) :=
  AsSmall.down ⋙ ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f).mapElements.op ⋙ AsSmall.up

/-- 同じ小さい比較も、元の右対象の射への後合成に厳密に自然。 -/
lemma smallToComma_naturality {V W : C} (f : V ⟶ W) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallElementsMap.{u, v, w} A f ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A W =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A V ⋙ CostructuredArrow.map (AsSmall.up.map f) := rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements
