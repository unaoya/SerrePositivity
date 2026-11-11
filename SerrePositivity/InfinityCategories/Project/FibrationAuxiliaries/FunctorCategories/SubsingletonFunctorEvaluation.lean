module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-!
概要：各次数の単体が一意な底からの関手空間は、指定した頂点で元の標的と厳密に同型。
方針：第二射影の curry を逆射とし、元の評価の往復を各次数で確認する。
規約：標的の充填性を仮定しない。
使われ方：零次元セル上の Cat∞ 値関手の評価の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 各次数の単体が一意な底での元の関手評価は、同じ標的への厳密な同型。 -/
def subsingletonFunctorEvaluationIso (B X : SSet.{u})
    [∀ n, Subsingleton (B.obj n)] (b : B _⦋0⦌) : (ihom B).obj X ≅ X where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b
  inv := curry (snd B X)
  hom_inv_id := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨t, F⟩
    change F.app (Opposite.op ⦋n⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n) =
      F.app (Opposite.op ⦋n⦌) (𝟙 _) t
    rw [Subsingleton.elim t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b n)]
  inv_hom_id := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex, lift_snd]

/-- 一点かつ全射が一意な通常圏の nerve の各次数の単体は一意。 -/
lemma nerve_obj_subsingleton_of_subsingletonCategory
    (C : Type u) [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (n : SimplexCategoryᵒᵖ) : Subsingleton ((nerve C).obj n) := by
  constructor
  intro F G
  refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _) ?_
  intro i j f
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
