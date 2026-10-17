import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- The target-isomorphism construction uses no model structure or monicity assumptions.
section GeneralIso
variable {V T P Q K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
  (e : P ≅ Q) (he : b ≫ e.hom = b') (s : K ⟶ RelativeChoiceSpace.obj i b')
example : RelativeChoiceSpace.obj i b ≅ RelativeChoiceSpace.obj i b' :=
  RelativeChoiceSpace.postIso i b b' e he
example : RelativeChoiceSpace.family i b (s ≫ (RelativeChoiceSpace.postIso i b b' e he).inv) =
    RelativeChoiceSpace.family i b' s ≫ e.inv :=
  RelativeChoiceSpace.family_postIso_inv i b b' e he s
end GeneralIso

section Context
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (Y : FramedResolution C) (W : ResolutionObject C) (g : Y.inner.base ⟶ W.base)

-- Arbitrary model source, independent object/Hom universes, small values.
example : (Over Y)ᵒᵖ × Under W ⥤ SSet.{v} := MixedChoiceFunctor.existingFunctor Y W g hcof
example : MixedChoiceFunctor.functor Y W g hcof ≅ MixedChoiceFunctor.existingFunctor Y W g hcof :=
  MixedChoiceFunctor.existingIso Y W g hcof
example : MixedChoiceFunctor.existingPoint Y W g hcof ≫
    MixedChoiceFunctor.existingProjection Y W g hcof = 𝟙 _ :=
  MixedChoiceFunctor.existingPoint_projection Y W g hcof
example (t : MixedChoiceFunctor.Context Y W) :
    (MixedChoiceFunctor.existingPoint Y W g hcof).app t =
      CoherentLiftMixedComparison.pointA hcof t.1.unop.left.inner Y.inner W t.2.right
        t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) :=
  MixedChoiceFunctor.existingPoint_component Y W g hcof t
example (t : MixedChoiceFunctor.Context Y W) (left : Bool) (k : Fin 3) :
    SSet.stdSimplex.δ k ≫ MixedChoiceFunctor.retainedTriangle Y W g hcof hfib t left =
      MixedChoiceFunctor.retain Y W g hcof t
        ((CoherentLiftMixedComparison.data hcof hfib t.1.unop.left.inner Y.inner W t.2.right
          t.1.unop.hom.map g t.2.hom (FramedResolution.frameMap t.1.unop.hom) left).faces k) :=
  MixedChoiceFunctor.retainedTriangle_face Y W g hcof hfib t left k
end Context

section GlobalComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X' X : FramedResolution C} {Y V W : ResolutionObject C} (a : X' ⟶ X)
  (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V) (b : V ⟶ W)

-- The entire previously chosen global triangle is recovered exactly.
example (left : Bool) : AllFactorizationMixedContext.triangle hcof hfib a f g b left ≫
    UniverseLift.map.{u} (AllFactorizationMixedContext.valueIso hcof a f g b).hom =
      AllFactorizationMixed.triangle hcof hfib a.map f g b (FramedResolution.frameMap a) left :=
  AllFactorizationMixedContext.triangle_recover hcof hfib a f g b left

-- In particular, the old source-changed postcomposition homotopy is an actual face.
example : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    AllFactorizationMixedContext.triangle hcof hfib a f g b true =
      ((AllFactorizationPost.homotopy hcof hfib (a.map.base ≫ f) g b).h ≫
        UniverseLift.map (CoherentLiftMixedComparison.mapBD hcof X'.inner X.inner Y W
          a.map f (g ≫ b) (FramedResolution.frameMap a))) ≫
        UniverseLift.map.{u} (AllFactorizationMixedContext.valueIso hcof a f g b).inv :=
  AllFactorizationMixedContext.triangle_AB hcof hfib a f g b

-- Every finite simplex is small, with all faces and degeneracies inherited from the global choice.
example (left : Bool) {n m : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ AllFactorizationMixedContext.simplex hcof hfib a f g b left c t =
      AllFactorizationMixedContext.simplex hcof hfib a f g b left (c.reindex θ.toOrderHom)
        ((SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).map θ.op t) :=
  AllFactorizationMixedContext.simplex_naturality hcof hfib a f g b left c t θ
end GlobalComparison

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceIso,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.MixedChoiceCompatibility,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationMixedContext]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some mixed choice modules were not audited"
  logInfo m!"Mixed choice compatibility audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
