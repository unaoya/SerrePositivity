module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberSquareIso

/-!
概要：通常の錐と native な錐の族の比較を構成する。
方針：指数比較と固定図式上の fiber の同型を使う。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の局所極限の双方向比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalClosed
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {I C : Type u} [Category.{u} I] [Category.{u} C] {F : I ⥤ C}

/-- 概要：指数比較は指定図式の頂点を保つ。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma nerveConeRestriction_vertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso I C).hom.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex F) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F) := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorCategoryIso_vertex F
/-- 概要：通常の制限の nerve の fiber と native な錐の族を同型にする。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
def nerveConeFiberFamilyIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneRestrictionFunctor (I := I) (C := C))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex F) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (nerveMap F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareIso _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeExtensionIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.nerveFunctorCategoryIso I C)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeRestriction_square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex F) ≪≫ eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (nerve I) (nerve C)))
      (nerveConeRestriction_vertex (F := F)))
/-- 概要：錐の族の同型は拡張関手への包含を保つ。
方針：指数比較と fiber の同型の射影公式を使う。
規約：同じ宇宙で元の指定図式と錐を保持する。
使われ方：B5 の局所極限と pointwise Kan の古典比較。 -/
lemma nerveConeFiberFamilyIso_inclusion : (nerveConeFiberFamilyIso (F := F)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction (nerve I) (nerve C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (nerveMap F)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneRestrictionFunctor (I := I) (C := C))) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex F) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveConeExtensionIso (I := I) (C := C)).hom := by
  dsimp only [nerveConeFiberFamilyIso]
  rw [Iso.trans_hom, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberι_eqTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction _ _)
    (nerveConeRestriction_vertex (F := F))]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberSquareIso_hom_inclusion _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
