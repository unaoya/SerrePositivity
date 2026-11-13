module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorComposition
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：相対関手空間の指定頂点での合成を実際の底上の射の合成として計算する。
方針：相対頂点の値を各入力で評価する。
規約：指定した射を保持。使われ方：coherent 三角形の全空間作用を具体的な射へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：相対豊穣合成は指定した二射の合成の相対頂点を返す。
方針：内部 Hom の全単体を評価して比較。
規約：厳密な頂点の等式。使われ方：指定三角形の合成比較の評価。 -/
lemma relativeFunctorComposition_vertex {B : SSet.{u}} (a b c : Over B)
    (f : a.left ⟶ b.left) (hf : f ≫ b.hom = a.hom)
    (g : b.left ⟶ c.left) (hg : g ≫ c.hom = b.hom) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex b.hom a.hom f hf, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex c.hom b.hom g hg) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex c.hom a.hom (f ≫ g)
          (by rw [Category.assoc, hg, hf]) := by
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro n α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
