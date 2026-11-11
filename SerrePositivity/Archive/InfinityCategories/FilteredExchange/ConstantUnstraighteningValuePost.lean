module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：定値標的への実作用の相対後合成を、同じ実作用の値への後合成へ厳密に移す。
方針：全係数の射影表示により、同じ相対後合成と内部 Hom の作用を比較する。
規約：元の実作用を保持。使われ方：単位作用と定値余極限辺の作用の整合の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 定値標的への相対実作用の後合成を値へ写すと、同じ実射と射影の後合成になる。 -/
lemma constantUnstraighteningRelativeIso_value_post {A E B : SSet.{u + 1}}
    (q : E ⟶ B) (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (f : E ⟶ leftUnstraightening (SSet.const z : B ⟶ SpaceInfinity))
    (hf : f ≫ leftUnstraighteningProjection (SSet.const z) = q) :
    HomotopyLimits.relativeFunctorPost q (leftUnstraighteningProjection (SSet.const z)) f hf a ≫
      ((constantUnstraighteningRelativeIso a z).hom ≫
        (ihom A).map (pointedSpaceFiberValueEquivalence z).hom) =
      vertexFiberι ((ihom A).map q) (functorVertex a) ≫
        (ihom A).map (f ≫ constantUnstraighteningFiberProjection B z ≫
          (pointedSpaceFiberValueEquivalence z).hom) := by
  simp only [constantUnstraighteningRelativeIso_value_eq_projection]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
