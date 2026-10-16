module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarContractionOperators

/-! # A single model-free simplicial contraction of the identity-projection bar

The full interval compatibility, including its mixed part, glues all
nerve-degree contractions into the actual diagonal homotopy.
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

/-- The same degreewise nerve interval, now natural in both simplicial directions together. -/
def identityHomotopyMap (d : D) :
    (relative (𝟭 D) F).obj d ⊗ SSet.stdSimplex.{max uD vD v}.obj (SimplexCategory.mk 1) ⟶
      (relative (𝟭 D) F).obj d where
  app n := (SerrePositivity.NerveHomotopy.hom (identityContraction F d n)).app n
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    let t := (SimplexCategory.toCat.map θ.unop).toFunctor
    let q := (SSet.stdSimplex.objEquiv x.2).toOrderHom.monotone.functor
    let z := (t ⋙ q).prod' (t ⋙ x.1)
    exact congrArg (fun J => z ⋙ J) (contractionInterval_operator F d θ).symm

lemma identityHomotopyMap_zero (d : D) :
    SSet.ι₀ ≫ identityHomotopyMap F d = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  have h := congrArg (fun k => k.app n c)
    (SerrePositivity.NerveHomotopy.at_zero (identityContraction F d n))
  exact h.trans (CategoryTheory.Functor.comp_id c)

lemma identityHomotopyMap_one (d : D) :
    SSet.ι₁ ≫ identityHomotopyMap F d =
      (identityAugmentation F).app d ≫ identitySection F d := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  have h := congrArg (fun k => k.app n c)
    (SerrePositivity.NerveHomotopy.at_one (identityContraction F d n))
  exact h.trans (identityCollapse_chain F d n c)

/-- An actual diagonal homotopy; it uses no model structure at the enlarged value universe. -/
def identityDiagonalHomotopy (d : D) :
    SSet.Homotopy (𝟙 ((relative (𝟭 D) F).obj d))
      ((identityAugmentation F).app d ≫ identitySection F d) where
  h := identityHomotopyMap F d
  h₀ := identityHomotopyMap_zero F d
  h₁ := identityHomotopyMap_one F d
  rel := by
    apply NatTrans.ext
    funext n
    refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
    exact False.elim x.1.property

end SerrePositivity.SimplicialModel.BarConstruction
