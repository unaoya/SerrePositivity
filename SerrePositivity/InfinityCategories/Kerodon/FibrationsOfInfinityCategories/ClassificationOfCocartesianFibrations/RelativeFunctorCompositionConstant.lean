module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：相対合成の第一成分を実射に固定すると、その実射による前合成となる。
方針：全ての内部 Hom の単体と入力で合成の評価を比較する。
規約：第二成分のパラメータは任意の単体集合全体を保つ。
使われ方：G8 の四角形①で、元の unstraightening の前合成比較を実射の前合成として読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 相対合成の第一成分を固定した全族は、同じ実射による前合成である。 -/
lemma relativeFunctorComposition_const_first {B K : SSet.{u}} (a b c : Over B)
    (f : a ⟶ b) (h : K ⟶ relativeFunctorSpace c.hom b.hom) :
    lift (SSet.const (relativeFunctorVertex b.hom a.hom f.left f.w)) h ≫
      relativeFunctorComposition a b c = h ≫ relativeFunctorOverPre c.hom f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro y
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
