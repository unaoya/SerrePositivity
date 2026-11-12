module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningValueOverPre

/-!
概要：定値相対 Hom の任意の fiber 値への作用と底上の前合成の可換性。
方針：相対同型の fiber 射影表示を使い、元の全係数の射を比較する。
規約：値への射を任意に保つ。使われ方：固定 native 値への定値三角形の射影。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 任意の元の fiber 射への後合成と、同じ底上の射による前合成の全族の可換性。 -/
lemma constantUnstraighteningRelativeIso_fiberMap_overPre {A C B X : SSet.{u + 1}}
    (p : A ⟶ B) (d : C ⟶ B) (t : C ⟶ A) (ht : t ≫ p = d)
    (z : SpaceInfinity.{u} _⦋0⦌) (g : vertexFiber pointedSpaceProjection z ⟶ X) :
    relativeFunctorOverPre (leftUnstraighteningProjection (SSet.const z : B ⟶ SpaceInfinity))
        (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht) ≫
      ((constantUnstraighteningRelativeIso d z).hom ≫ (ihom C).map g) =
      ((constantUnstraighteningRelativeIso p z).hom ≫ (ihom A).map g) ≫ (pre t).app X := by
  simp only [constantUnstraighteningRelativeIso_hom_eq_projection, Category.assoc]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 任意の fiber 射への作用も、同じ fiber 包含と元の射影による後合成。 -/
lemma constantUnstraighteningRelativeIso_fiberMap_eq_projection {A B X : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌)
    (g : vertexFiber pointedSpaceProjection z ⟶ X) :
    (constantUnstraighteningRelativeIso a z).hom ≫ (ihom A).map g =
      vertexFiberι ((ihom A).map (leftUnstraighteningProjection
        (SSet.const z : B ⟶ SpaceInfinity))) (functorVertex a) ≫
          (ihom A).map (constantUnstraighteningFiberProjection B z ≫ g) := by
  rw [constantUnstraighteningRelativeIso_hom_eq_projection, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.InfinityCategories.F2
