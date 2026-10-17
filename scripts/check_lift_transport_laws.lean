import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Transport of an already specified comparison face, without any model input.
example {V T P Q K L : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q)
    (q : P ⟶ Q) (hq : b ≫ q = b') (j : K ⟶ L)
    (a : K ⟶ RelativeChoiceSpace.obj i b) (e : L ⟶ RelativeChoiceSpace.obj i b) (he : j ≫ e = a) :
    T ◁ j ≫ RelativeChoiceSpace.family i b' (e ≫ RelativeChoiceSpace.postMap i b b' q hq) =
      RelativeChoiceSpace.family i b a ≫ q := by
  rw [RelativeChoiceSpace.family_postMap, ← Category.assoc,
    ← RelativeChoiceSpace.family_naturality, he]

-- Source restriction transports the actual evaluated family, rather than
-- selecting a new homotopic family. All boundary data are explicit squares.
example {V T V' T' P K : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P)
    (i' : V' ⟶ T') (b' : V' ⟶ P) (v : V' ⟶ V) (t : T' ⟶ T)
    (hi : i' ≫ t = v ≫ i) (hb : v ≫ b = b') (s : K ⟶ RelativeChoiceSpace.obj i b) :
    RelativeChoiceSpace.family i' b' (s ≫ RelativeChoiceSpace.preMap i b i' b' v t hi hb) =
      t ▷ K ≫ RelativeChoiceSpace.family i b s :=
  RelativeChoiceSpace.family_preMap i b i' b' v t hi hb s

-- Strict functoriality for codomain transport of whole comparison spaces.
example {V T P Q R : SSet.{v}} (i : V ⟶ T) (b : V ⟶ P) (b' : V ⟶ Q) (b'' : V ⟶ R)
    (q : P ⟶ Q) (r : Q ⟶ R) (hq : b ≫ q = b') (hr : b' ≫ r = b'') :
    RelativeChoiceSpace.postMap i b b' q hq ≫ RelativeChoiceSpace.postMap i b' b'' r hr =
      RelativeChoiceSpace.postMap i b b'' (q ≫ r) (by rw [← Category.assoc, hq, hr]) :=
  RelativeChoiceSpace.postMap_compose i b b' b'' q r hq hr

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- Ordinary arbitrary model source only: actual frame composites, with explicit
-- base reassociation, give the exact contravariant transport composition.
example (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y ⟶ W) (h : W.base ⟶ V.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) (ψ : ResolutionLiftPrecomposition.FrameMap g) :
    ResolutionLiftPrecomposition.map Y W V g h ψ ≫
        ResolutionLiftPrecomposition.map X Y V f (g.base ≫ h) φ =
      ResolutionLiftPrecomposition.map X W V (f ≫ g) h
        (ResolutionLiftPrecomposition.compose φ ψ) ≫
          ResolutionLiftSpace.baseChange (Category.assoc f.base g.base h) :=
  ResolutionLiftFunctorLaws.pre_compose X Y W V f g h φ ψ

example (X Y W V : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (h : W ⟶ V) :
    ResolutionLiftPostcomposition.map X Y W f g ≫
        ResolutionLiftPostcomposition.map X W V (f ≫ g.base) h ≫
          ResolutionLiftSpace.baseChange (Category.assoc f g.base h.base) =
      ResolutionLiftPostcomposition.map X Y V f (g ≫ h) :=
  ResolutionLiftFunctorLaws.post_compose X Y W V f g h

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Keep the actual chosen comparison parameter and both prescribed endpoints.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ CoherentLiftRelative.postEdge hcof hfib X Y W f g =
        CoherentLiftRelative.postLeftPoint hcof X Y W f g ∧
      SSet.stdSimplex.δ (0 : Fin 2) ≫ CoherentLiftRelative.postEdge hcof hfib X Y W f g =
        CoherentLiftRelative.postRightPoint hcof X Y W f g :=
  ⟨CoherentLiftRelative.postEdge_at_zero hcof hfib X Y W f g,
    CoherentLiftRelative.postEdge_at_one hcof hfib X Y W f g⟩

example (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ CoherentLiftRelative.preEdge hcof hfib X Y W f g φ =
        CoherentLiftRelative.preLeftPoint hcof X Y W f g φ ∧
      SSet.stdSimplex.δ (0 : Fin 2) ≫ CoherentLiftRelative.preEdge hcof hfib X Y W f g φ =
        CoherentLiftRelative.preRightPoint hcof X Y W f g :=
  ⟨CoherentLiftRelative.preEdge_at_zero hcof hfib X Y W f g φ,
    CoherentLiftRelative.preEdge_at_one hcof hfib X Y W f g φ⟩

-- The actual mixed interchange acts identically in the existing Kan targets,
-- with no replacement of the parameter, no fibrancy condition on Z, and no
-- source functorial factorization assumption.
example (X Y W V : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (h : W ⟶ V)
    (φ : ResolutionLiftPrecomposition.FrameMap f) (Z : C) {T : SSet.{v}}
    (s : T ⟶ ResolutionLiftSpace.obj Y W g)
    (t : T ⟶ (cosimplicialHom V.resolution.obj).obj Z) :
    KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z
        (s ≫ (ResolutionLiftPrecomposition.map X Y W f g φ ≫
          ResolutionLiftPostcomposition.map X W V (f.base ≫ g) h ≫
            ResolutionLiftSpace.baseChange (Category.assoc f.base g h.base))) t =
      KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z
        (s ≫ (ResolutionLiftPostcomposition.map Y W V g h ≫
          ResolutionLiftPrecomposition.map X Y V f (g ≫ h.base) φ)) t :=
  congrArg (fun k => KanLiftAction.parameterized hcof hfib X V (f.base ≫ g ≫ h.base) Z (s ≫ k) t)
    (ResolutionLiftFunctorLaws.interchange X Y W V f g h φ)

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftEdges,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceMaps,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftFunctorLaws]
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
  unless modules.size == expected.size do throwError "Some lift transport modules were not audited"
  logInfo m!"Lift transport law audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
