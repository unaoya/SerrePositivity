module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying

/-!
概要：相対 curry と定値標的の fiber 表示は全係数で厳密に可換する。
方針：元の fiber 射影の表示へ戻し、同じ三変数の全評価を比較する。
規約：元の相対 curry と指定同型を保持。使われ方：三角形比較の curry と輸送比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 相対 curry の定値 fiber 表示は、同じ全 fiber 評価を通常の curry で写したもの。 -/
lemma relativeFunctorCurryHom_constant_fiber {A B K : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    relativeFunctorCurryHom
        (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity)) a K ≫
      (ihom K).map (constantUnstraighteningRelativeIso a z).hom =
    (constantUnstraighteningRelativeIso (fst A K ≫ a) z).hom ≫
      functorSpaceCurryMap A K (vertexFiber pointedSpaceProjection z) := by
  rw [constantUnstraighteningRelativeIso_hom_eq_projection a z,
    constantUnstraighteningRelativeIso_hom_eq_projection (fst A K ≫ a) z]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro k
  apply CategoryTheory.Functor.functorHom_ext
  intro d β
  apply ConcreteCategory.hom_ext
  intro e
  rfl

end SerrePositivity.InfinityCategories.F2
