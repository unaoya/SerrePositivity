module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorEnrichedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：相対合成の第二成分を実射に固定すると、その実射による後合成となる。
方針：全ての内部 Hom の単体と入力で合成の評価を比較する。
規約：第一成分のパラメータは任意の単体集合全体を保つ。
使われ方：G14 で、元の unstraightening の後合成比較を実射の後合成として読む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 相対合成の第二成分を固定した族は、同じ底上の射による後合成。 -/
lemma relativeFunctorComposition_const_second {B K : SSet.{u}} (a b c : Over B)
    (f : b ⟶ c) (h : K ⟶ relativeFunctorSpace b.hom a.hom) :
    lift h (SSet.const (relativeFunctorVertex c.hom b.hom f.left f.w)) ≫
      relativeFunctorComposition a b c = h ≫
        SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost
          b.hom c.hom f.left f.w a.hom := by
  have hv : (SSet.const (relativeFunctorVertex c.hom b.hom f.left f.w) :
      K ⟶ relativeFunctorSpace c.hom b.hom) ≫ relativeFunctorPostHom a b c =
      SSet.const (functorVertex
        (SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost
          b.hom c.hom f.left f.w a.hom)) := by
    rw [SSet.const_comp, relativeFunctorPostHom_vertex]
  have he := congrArg uncurry hv
  rw [relativeFunctorPostHom, uncurry_natural_left, uncurry_curry,
    SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex] at he
  have hq := congrArg (fun q => lift h (𝟙 K) ≫ q) he
  simpa only [← Category.assoc, lift_whiskerLeft, Category.id_comp, lift_fst] using hq

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
