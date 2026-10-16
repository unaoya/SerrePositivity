import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.NerveSimplexEndpoint

section ModelFreeRelative
-- No model structure on the value universe is supplied.
variable {D : Type uD} [Category.{vD} D] (F G : D ⥤ SSet.{v}) (p : F ⟶ G)
  (hp : ∀ d, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app d))
  (target : NerveCoherentFamily.System G) (n : ℕ) (old : NerveLowerExtension.LowerSystem F n)
  (hboundary : old ≫ Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveMonomorphismLifting.valueMap F G p) =
      Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n) target)

example : NerveMonomorphismLifting.extend F G p target n old hboundary hp ≫
    NerveMonomorphismLifting.valueMap F G p = target :=
  NerveMonomorphismLifting.extend_boundary _ _ _ _ _ _ _ _

example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveMonomorphismLifting.extend F G p target n old hboundary hp) = old :=
  NerveMonomorphismLifting.extend_restrict _ _ _ _ _ _ _ _
end ModelFreeRelative

section LargeParameter
-- Only boundary fillers of the original small values are inputs.
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  (hp : ∀ d, UniverseLift.BoundaryFillers (F.obj d)) (K : SSet.{max w v})
  (families : ∀ d, K ⟶ UniverseLift.obj.{w} (F.obj d))

example (d : D) : NerveParameterExtension.evaluate (NerveLargeParameter.lifted F)
    (NerveLargeParameter.extendFamilies F hp K families) d = families d :=
  NerveLargeParameter.extendFamilies_evaluate _ _ _ _ d

variable {A : SSet.{max w v}} (i : A ⟶ K) [Mono i]
  (boundary : NerveLargeParameter.System F A) (n : ℕ)
  (old : NerveLowerExtension.LowerSystem (NerveLargeParameter.mapping F K) n)
  (hboundary : old ≫ Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveMonomorphismLifting.valueMap (NerveLargeParameter.mapping F K)
      (NerveLargeParameter.mapping F A)
      (NerveParameterExtension.restriction (NerveLargeParameter.lifted F) i)) =
        Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n) boundary)

example : NerveLargeParameter.relative F hp K i boundary n old hboundary ≫
    NerveMonomorphismLifting.valueMap _ _
      (NerveParameterExtension.restriction (NerveLargeParameter.lifted F) i) = boundary :=
  NerveLargeParameter.relative_boundary _ _ _ _ _ _ _ _

example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
    (NerveLargeParameter.relative F hp K i boundary n old hboundary) = old :=
  NerveLargeParameter.relative_restrict _ _ _ _ _ _ _ _
end LargeParameter

section ActualGlobalSquare
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : FramedResolution C) (Y V : ResolutionObject C) (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V)
open AllFactorizationCoherentSquare

example (left : Bool) (t : Context X V) :
    NerveParameterExtension.evaluate (NerveLargeParameter.lifted (values hcof X Y V f g))
      (triangle hcof hfib X Y V f g left) t ≫
        UniverseLift.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    AllFactorizationMixed.triangle hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom) left :=
  triangle_recover _ _ _ _ _ _ _ left t

-- Both entire triangles share one entire diagonal system in every external degree.
example : NerveLargeParameter.restrict (values hcof X Y V f g)
    (triangle hcof hfib X Y V f g true) (diagonalParameter Y V g) =
    NerveLargeParameter.restrict (values hcof X Y V f g)
      (triangle hcof hfib X Y V f g false) (diagonalParameter Y V g) :=
  shared_diagonal _ _ _ _ _ _ _

-- Every finite parameter simplex is retained in the original Hom universe.
example (left : Bool) (t : Context X V) {n : ℕ} (c : AnchoredChain g n)
    (q : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    simplex hcof hfib X Y V f g left t c q =
    AllFactorizationMixed.simplex hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom) left c q := simplex_recover _ _ _ _ _ _ _ left t c q

-- All external faces and degeneracies act on the same whole global square.
example {n m : ℕ} (c : ComposableArrows (Context X V) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ (square hcof hfib X Y V f g).app (ofChain c) =
    (square hcof hfib X Y V f g).app
      (ofChain ((SimplexCategory.toCat.map θ).toFunctor ⋙ c)) ≫
      (NerveLargeParameter.mapping (values hcof X Y V f g) _).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveCoherentFamily.reindex_compatibility _ _ c θ

-- Retain all four originally selected global pre/post homotopies, not pointwise replacements.
example (t : Context X V) :
    NerveParameterExtension.evaluate (NerveLargeParameter.lifted (values hcof X Y V f g))
      (edge hcof hfib X Y V f g true 2) t ≫
        UniverseLift.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    (AllFactorizationPost.homotopy hcof hfib (t.1.unop.hom.map.base ≫ f) g t.2.hom).h ≫
      UniverseLift.map (CoherentLiftMixedComparison.mapBD hcof t.1.unop.left.inner X.inner Y
        t.2.right t.1.unop.hom.map f (g ≫ t.2.hom) (FramedResolution.frameMap t.1.unop.hom)) :=
  (edge_recover hcof hfib X Y V f g true 2 t).trans
    (AllFactorizationMixed.triangle_AB hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom))

example (t : Context X V) :
    NerveParameterExtension.evaluate (NerveLargeParameter.lifted (values hcof X Y V f g))
      (edge hcof hfib X Y V f g true 0) t ≫
        UniverseLift.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    (AllFactorizationPre.homotopy hcof hfib t.1.unop.hom.map f g
      (FramedResolution.frameMap t.1.unop.hom)).h ≫
        AllFactorizationMixed.valueMap hcof t.1.unop.hom.map f g t.2.hom
          (FramedResolution.frameMap t.1.unop.hom) :=
  (edge_recover hcof hfib X Y V f g true 0 t).trans
    (AllFactorizationMixed.triangle_BD hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom))

example (t : Context X V) :
    NerveParameterExtension.evaluate (NerveLargeParameter.lifted (values hcof X Y V f g))
      (edge hcof hfib X Y V f g false 2) t ≫
        UniverseLift.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    AllFactorizationMixed.chainMap g t.2.hom ▷
      SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
        (AllFactorizationPre.homotopy hcof hfib t.1.unop.hom.map f (g ≫ t.2.hom)
          (FramedResolution.frameMap t.1.unop.hom)).h :=
  (edge_recover hcof hfib X Y V f g false 2 t).trans
    (AllFactorizationMixed.triangle_AC hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom))

example (t : Context X V) :
    NerveParameterExtension.evaluate (NerveLargeParameter.lifted (values hcof X Y V f g))
      (edge hcof hfib X Y V f g false 0) t ≫
        UniverseLift.map.{u}
          (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    (AllFactorizationPost.homotopy hcof hfib f g t.2.hom).h ≫
      UniverseLift.map (CoherentLiftMixedComparison.mapAC t.1.unop.left.inner X.inner Y
        t.2.right t.1.unop.hom.map f (g ≫ t.2.hom) (FramedResolution.frameMap t.1.unop.hom)) :=
  (edge_recover hcof hfib X Y V f g false 0 t).trans
    (AllFactorizationMixed.triangle_CD hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom))

end ActualGlobalSquare

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexMonomorphismLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMonomorphismLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryFillerLifting,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveFillerExtension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveLargeParameter,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationCoherentSquare]
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
    throwError "Some large parameter coherence modules were not audited"
  logInfo m!"Large parameter coherence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
