module

public import SerrePositivity.CategoryTheory.AnchoredChainTransport
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftTensor

/-! # Whole finite test parameters of the actual large factorization-chain space -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SerrePositivity.SimplicialModel.UniverseLift

/-- The same lifted small set with an already absorbed universe level relabelled. -/
def stableIso (P : SSet.{v}) : obj.{u} P ≅ obj.{max u v} P :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun x => ULift.up x.down
      invFun := fun x => ULift.up x.down
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }) (by intro n m θ; ext x; rfl)

lemma stableIso_naturality {P Q : SSet.{v}} (f : P ⟶ Q) :
    map.{u} f ≫ (stableIso Q).hom = (stableIso P).hom ≫ map.{max u v} f := by
  ext n x
  rfl

end SerrePositivity.SimplicialModel.UniverseLift

namespace SerrePositivity.SimplicialModel.AnchoredChainFiniteTest
variable {D : Type u} [Category.{v} D] {Y V : D} (g : Y ⟶ V)

abbrev smallParameter (m r : ℕ) : SSet.{v} :=
  SSet.stdSimplex.obj (SimplexCategory.mk m) ⊗ SSet.stdSimplex.obj (SimplexCategory.mk r)
abbrev parameter (r : ℕ) := AnchoredChain.simplicial g ⊗
  SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk r)

abbrev simplex {m : ℕ} (c : AnchoredChain g m) :
    UniverseLift.obj.{u} (SSet.stdSimplex.{v}.obj (SimplexCategory.mk m)) ⟶
      AnchoredChain.simplicial g :=
  (UniverseLift.stdIso m).hom ≫ (SSet.yonedaEquiv (X := AnchoredChain.simplicial g)).symm c

lemma simplex_reindex {m n : ℕ} (c : AnchoredChain g m)
    (ψ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    UniverseLift.map.{u} (SSet.stdSimplex.map ψ) ≫ simplex g c =
      simplex g (c.reindex ψ.toOrderHom) := by
  change UniverseLift.map.{u} (SSet.stdSimplex.map ψ) ≫
    ((UniverseLift.stdIso m).hom ≫ (SSet.yonedaEquiv (X := AnchoredChain.simplicial g)).symm c) = _
  rw [← Category.assoc]
  have hu : UniverseLift.map.{u} (SSet.stdSimplex.{v}.map ψ) ≫
      (UniverseLift.stdIso m).hom = (UniverseLift.stdIso n).hom ≫ SSet.stdSimplex.map ψ := rfl
  rw [hu, Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  rfl

/-- Keep the entire supplementary simplex, not just its vertices or sampled points. -/
def test {m : ℕ} (c : AnchoredChain g m) (r : ℕ) :
    UniverseLift.obj.{u} (smallParameter.{v} m r) ⟶ parameter g r :=
  (UniverseLift.tensorIso (SSet.stdSimplex.{v}.obj (SimplexCategory.mk m))
    (SSet.stdSimplex.obj (SimplexCategory.mk r))).hom ≫
    (simplex g c ▷ UniverseLift.obj.{u} (SSet.stdSimplex.obj (SimplexCategory.mk r))) ≫
    (AnchoredChain.simplicial g ◁ (UniverseLift.stdIso r).hom)

lemma test_operator {m r s : ℕ} (c : AnchoredChain g m)
    (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk s) :
    UniverseLift.map.{u} (SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.map θ) ≫
      test g c s = test g c r ≫ AnchoredChain.simplicial g ◁ SSet.stdSimplex.map θ := by
  apply NatTrans.ext
  funext n
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  rfl

lemma test_reindex {m n : ℕ} (c : AnchoredChain g m)
    (ψ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (r : ℕ) :
    UniverseLift.map.{u} (SSet.stdSimplex.map ψ ▷ SSet.stdSimplex.obj (SimplexCategory.mk r)) ≫
      test g c r = test g (c.reindex ψ.toOrderHom) r := by
  apply NatTrans.ext
  funext d
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  apply Prod.ext
  · exact congrArg (fun z => z.app d (ULift.up x.down.1)) (simplex_reindex g c ψ)
  · rfl

end SerrePositivity.SimplicialModel.AnchoredChainFiniteTest
