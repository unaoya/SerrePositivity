module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ConstantDiagramTransportWitness

/-!
概要：定値標的の相対 Hom 同型の射を、fiber 射影による後合成へ厳密に同定する。
方針：全係数の uncurry 評価を恒等族に適用し、fiber の包含後で比較する。
規約：元の射影と同型を保持。使われ方：上下面の比較を同じ全空間作用で写す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全相対 Hom 上の指定同型の射は、元の fiber 射影の内部 Hom 上の作用そのもの。 -/
lemma constantUnstraighteningRelativeIso_hom_eq_projection {A B : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    (constantUnstraighteningRelativeIso a z).hom =
      vertexFiberι ((ihom A).map (leftUnstraighteningProjection
        (SSet.const z : B ⟶ SpaceInfinity))) (functorVertex a) ≫
          (ihom A).map (constantUnstraighteningFiberProjection B z) := by
  have h := constantUnstraighteningRelativeIso_uncurry a z
    (𝟙 (relativeFunctorSpace (leftUnstraighteningProjection
      (SSet.const z : B ⟶ SpaceInfinity)) a))
  simp only [Category.id_comp, relativeFunctorUncurry] at h
  apply uncurry_injective
  apply vertexFiber_hom_ext pointedSpaceProjection z
  rw [uncurry_natural_right, Category.assoc, constantUnstraighteningFiberProjection,
    Category.assoc, constantPullbackFiberIso_fst_ι]
  exact h

/-- 同じ相対 Hom 同型から元の値への作用は、fiber 射影と値の比較による後合成。 -/
lemma constantUnstraighteningRelativeIso_value_eq_projection {A B : SSet.{u + 1}}
    (a : A ⟶ B) (z : SpaceInfinity.{u} _⦋0⦌) :
    (constantUnstraighteningRelativeIso a z).hom ≫
        (ihom A).map (pointedSpaceFiberValueEquivalence z).hom =
      vertexFiberι ((ihom A).map (leftUnstraighteningProjection
        (SSet.const z : B ⟶ SpaceInfinity))) (functorVertex a) ≫
          (ihom A).map (constantUnstraighteningFiberProjection B z ≫
            (pointedSpaceFiberValueEquivalence z).hom) := by
  rw [constantUnstraighteningRelativeIso_hom_eq_projection, Category.assoc,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.InfinityCategories.F2
