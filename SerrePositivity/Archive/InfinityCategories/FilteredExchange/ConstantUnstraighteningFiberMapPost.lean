module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ConstantUnstraighteningFiberMapOverPre
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：定値標的への相対後合成を、任意の同じ fiber 射への実後合成として計算する。
方針：全係数の fiber 射影表示で元の実射を比較する。
規約：実射・値射を保持。使われ方：五因子式の最初辺を実際の後合成へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 定値標的への相対後合成と任意の fiber 値への射影は、同じ実射の後合成。 -/
lemma constantUnstraighteningRelativeIso_fiberMap_post {A E B X : SSet.{u + 1}}
    (q : E ⟶ B) (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (f : E ⟶ leftUnstraightening (SSet.const z : B ⟶ SpaceInfinity))
    (hf : f ≫ leftUnstraighteningProjection (SSet.const z) = q)
    (g : vertexFiber pointedSpaceProjection z ⟶ X) :
    HomotopyLimits.relativeFunctorPost q (leftUnstraighteningProjection (SSet.const z)) f hf a ≫
      ((constantUnstraighteningRelativeIso a z).hom ≫ (ihom A).map g) =
      vertexFiberι ((ihom A).map q) (functorVertex a) ≫
        (ihom A).map (f ≫ constantUnstraighteningFiberProjection B z ≫ g) := by
  simp only [constantUnstraighteningRelativeIso_fiberMap_eq_projection]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
