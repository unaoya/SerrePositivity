import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Large parameters and independently sized indices require no simplicial model structure.
section IndependentUniverses
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})
  {K : SSet.{max w v}} (a : NerveLargeParameter.System.{w, v} F K)
  {P : SSet.{v}} (k : UniverseLift.obj.{w} P ⟶ K)
example {n : ℕ} (c : ComposableArrows D n) :
    P ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ F.obj (c.obj (Fin.last n)) :=
  NerveLargeSampling.family F a k c
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    P ◁ SSet.stdSimplex.map θ ≫ NerveLargeSampling.family F a k c =
    NerveLargeSampling.family F a k ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      F.map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last m))))) :=
  NerveLargeSampling.family_naturality F a k c θ
example {Q : SSet.{v}} (q : Q ⟶ P) {n : ℕ} (c : ComposableArrows D n) :
    NerveLargeSampling.family F a (UniverseLift.map.{w} q ≫ k) c =
      (q ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ NerveLargeSampling.family F a k c :=
  NerveLargeSampling.family_precomp F a k q c
end IndependentUniverses

section WholeFactorizationSquare
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : FramedResolution C) (Y V : ResolutionObject C) (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V)
open AllFactorizationCoherentSquare

section
open AllFactorizationSmallFamilies

example (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    smallParameter.{v} m 2 ◁ SSet.stdSimplex.map θ ≫ family hcof hfib X Y V f g side d c =
    family hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      (values hcof X Y V f g).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l))))) :=
  AllFactorizationSmallFamilies.external_naturality hcof hfib X Y V f g side d c θ

example (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) :
    ((SSet.stdSimplex.map ψ ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family hcof hfib X Y V f g side d c =
    family hcof hfib X Y V f g side (d.reindex ψ.toOrderHom) c :=
  AllFactorizationSmallFamilies.factor_naturality hcof hfib X Y V f g side d c ψ

example (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.δ k) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family hcof hfib X Y V f g side d c =
    faceFamily hcof hfib X Y V f g side k d c :=
  AllFactorizationSmallFamilies.family_face hcof hfib X Y V f g side k d c

example (side : Bool) {m : ℕ} (d : AnchoredChain g m) (t : Context X V) :
    UniverseLift.map.{u} (point hcof hfib X Y V f g side d t) ≫
      UniverseLift.map.{u}
        (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    test g d 2 ≫ AllFactorizationMixed.triangle hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom) side :=
  AllFactorizationSmallFamilies.original_recover hcof hfib X Y V f g side d t
end

section
open AllFactorizationSmallAction

example (side : Bool) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    (CoherentLiftRelative.vertexInclusion X.inner Y f ▷
      (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ⊗
        SSet.stdSimplex.obj (SimplexCategory.mk n))) ≫ rawFamily hcof hfib X Y V f g side d c =
    CoherentLiftRelative.vertices X.inner Y f ◁
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
      (ρ_ _).hom ≫ (MixedChoiceFunctor.boundary X Y f hcof).app
        ((contexts X Y V g).obj (c.obj (Fin.last n))) :=
  AllFactorizationSmallAction.raw_vertices hcof hfib X Y V f g side d c

example (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n)
    (Z : C) (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
      SSet.stdSimplex.map θ) ≫ action hcof hfib X Y V f g side d c Z t =
    ResolutionArrowActionTransport.kan C hcof hfib
      ((centers X Y V f g).obj (c.obj (θ.toOrderHom (Fin.last l)))) Z
      (liftFamily hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))
      (((tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
        SSet.stdSimplex.map θ)) ≫ t) ≫
        inputMap X Y V f g c θ Z) ≫
      outputMap hcof hfib X Y V f g c θ Z :=
  AllFactorizationSmallAction.action_external hcof hfib X Y V f g side d c θ Z t

example (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
    (Z : C) (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    tupleParameter X Y f ◁ ((SSet.stdSimplex.map ψ ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      action hcof hfib X Y V f g side d c Z t =
    action hcof hfib X Y V f g side (d.reindex ψ.toOrderHom) c Z
      ((tupleParameter X Y f ◁ ((SSet.stdSimplex.map ψ ▷
        SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷
          SSet.stdSimplex.obj (SimplexCategory.mk n))) ≫ t) :=
  AllFactorizationSmallAction.action_factor hcof hfib X Y V f g side d c ψ Z t

example (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (Z : C)
    (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    tupleParameter X Y f ◁ ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.δ k) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ action hcof hfib X Y V f g side d c Z t =
    faceAction hcof hfib X Y V f g side k d c Z
      ((tupleParameter X Y f ◁ ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁
        SSet.stdSimplex.δ k) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n))) ≫ t) :=
  AllFactorizationSmallAction.action_face hcof hfib X Y V f g side k d c Z t

example {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (Z : C)
    (t : faceParameter X Y f m n ⟶ input X Y V f g c Z) :
    faceAction hcof hfib X Y V f g true 1 d c Z t =
      faceAction hcof hfib X Y V f g false 1 d c Z t :=
  AllFactorizationSmallAction.shared_diagonal hcof hfib X Y V f g d c Z t

example {n : ℕ} (c : ComposableArrows (Context X V) n) (Z : C) :
    SSet.KanComplex (output hcof hfib X Y V f g c Z) :=
  AllFactorizationSmallAction.output_kanComplex hcof hfib X Y V f g c Z
end
end WholeFactorizationSquare

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.NerveLargeSampling,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.AnchoredChainFiniteTest,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallFamilies,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AllFactorizationSmallAction]
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
    throwError "Some whole factorization action modules were not audited"
  logInfo m!"Whole factorization small action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
