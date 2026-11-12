module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MappingParameters

/-!
概要：区間写像空間の族と h Fun の Hom の表示のパラメータ自然性。
方針：前合成の内部 Hom の射と curry の自然性を比較する。
規約：quasicategory 性を要求しない段階で計算する。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータ付き adjunct 対応。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：定値関手間の h Fun の射をパラメータの射で前合成する。
方針：内部 Hom の前合成作用をホモトピー圏へ移す。
規約：両端の定値関手は同じ頂点 x,y のまま。
使われ方：区間模型の族の表示の自然性。 -/
def intervalFamilyHomPrecomp {A B X : SSet.{u}} {x y : X _⦋0⦌} (i : A ⟶ B)
    (α : (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : B ⟶ X)) :
      hoFunctor.obj ((ihom B).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y))) :
    (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : A ⟶ X)) :
      hoFunctor.obj ((ihom A).obj X)) ⟶
        SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y)) :=
  (hoFunctor.map ((pre i).app X)).toFunctor.map α

/-- 概要：族が表す h Fun の射はパラメータの前合成と整合する。
方針：代表辺で内部 Hom の前合成と curry の自然性を比較する。
規約：A,B,X は任意の単体集合。
使われ方：Kerodon Prop 6.2.1.17（Tag 02F1） のパラメータに自然な Hom の表示。 -/
lemma intervalFamilyHom_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (i ≫ f) = intervalFamilyHomPrecomp i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom f) := by
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
