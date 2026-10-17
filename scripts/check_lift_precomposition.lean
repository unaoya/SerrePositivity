import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

-- The shared pullback-fiber construction works in a bare locally small category.
example {C : Type u} [Category.{v} C] (A A' : SimplexCategory ⥤ C) {X Y E B : C}
    (a : A ⟶ (Functor.const SimplexCategory).obj X)
    (a' : A' ⟶ (Functor.const SimplexCategory).obj Y) (k : X ⟶ Y) (φ : A ⟶ A')
    (hφ : φ ≫ a' = a ≫ (Functor.const SimplexCategory).map k)
    (p : E ⟶ B) (fX : X ⟶ B) (fY : Y ⟶ B) (hf : k ≫ fY = fX) :
    LiftSpace.obj A' a' p fY ⟶ LiftSpace.obj A a p fX :=
  LiftSpacePrecomposition.map A A' a a' k φ hφ p fX fY hf

-- Outer lift existence uses the ordinary model structure alone.
example {C : Type u} [Category.{v} C] [ModelCategory C]
    {X Y : ResolutionObject C} (f : X ⟶ Y) :
    ResolutionLiftPrecomposition.FrameMap f := ResolutionLiftPrecomposition.lift f

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- A constructed outer lift gives an actual map between the existing Kan
-- target models, compatible with their original resolution Hom comparisons.
example {X Y : ResolutionObject C} (f : X ⟶ Y) (Z : C) [IsFibrant Z]
    (hf : weakEquivalences C f.base) :
    ∃ t : KanLiftAction.target hcof hfib Y Z ⟶ KanLiftAction.target hcof hfib X Z,
      (cosimplicialHomMap f.diagram).app Z ≫ KanLiftAction.comparison hcof hfib X Z =
        KanLiftAction.comparison hcof hfib Y Z ≫ t ∧ weakEquivalences SSet.{v} t := by
  let φ := ResolutionLiftPrecomposition.lift f
  exact ⟨ResolutionLiftPrecomposition.kanTargetMap hcof hfib f φ Z,
    ResolutionLiftPrecomposition.kan_comparison hcof hfib f φ Z,
    ResolutionLiftPrecomposition.kanTargetMap_weakEquivalence hcof hfib f φ hf Z⟩

-- Exact source change for entire parameterized higher families.
example (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) (Z : C) {T : SSet.{v}}
    (s : T ⟶ ResolutionLiftSpace.obj Y W g)
    (t : T ⟶ (cosimplicialHom W.resolution.obj).obj Z) :
    KanLiftAction.parameterized hcof hfib X W (f.base ≫ g) Z
        (s ≫ ResolutionLiftPrecomposition.map X Y W f g φ) t =
      KanLiftAction.parameterized hcof hfib Y W g Z s t ≫
        ResolutionLiftPrecomposition.kanTargetMap hcof hfib f φ Z :=
  ResolutionLiftPrecomposition.kan_action hcof hfib X Y W f g φ Z s t

-- Strict vertices precompose to the actual composite resolution map.
example {X Y W : ResolutionObject C} (f : X ⟶ Y) (g : Y ⟶ W)
    (φ : ResolutionLiftPrecomposition.FrameMap f) :
    ResolutionLiftSpace.ofLift g ≫ ResolutionLiftPrecomposition.map X Y W f g.base φ =
      ResolutionLiftSpace.ofLift (f ≫ g) := ResolutionLiftPrecomposition.ofLift f g φ

-- Precomposition retains previously prescribed higher boundary data.
example (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base)
    (φ : ResolutionLiftPrecomposition.FrameMap f) {K L : SSet.{v}} (i : K ⟶ L) [Mono i]
    (b : K ⟶ ResolutionLiftSpace.obj Y W g) :
    ∃ e : L ⟶ ResolutionLiftSpace.obj Y W g,
      i ≫ (e ≫ ResolutionLiftPrecomposition.map X Y W f g φ) =
        b ≫ ResolutionLiftPrecomposition.map X Y W f g φ := by
  obtain ⟨e, he⟩ := ResolutionLiftSpace.extension hcof Y W g i b
  exact ⟨e, ResolutionLiftPrecomposition.boundary X Y W f g φ i b e he⟩

-- Target naturality is a natural transformation of the actual Kan-valued functors.
example {X Y : ResolutionObject C} (f : X ⟶ Y)
    (φ : ResolutionLiftPrecomposition.FrameMap f) {Z Z' : C} (h : Z ⟶ Z') :
    (KanLiftAction.targetFunctor hcof hfib Y).map h ≫
        ResolutionLiftPrecomposition.kanTargetMap hcof hfib f φ Z' =
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib f φ Z ≫
        (KanLiftAction.targetFunctor hcof hfib X).map h :=
  (ResolutionLiftPrecomposition.kanTargetNatTrans hcof hfib f φ).naturality h

-- Actual identity/composite frame maps give strict source laws. These tests
-- do not replace them with independently chosen lifts of identity/composite.
example (X : ResolutionObject C) (Z : C) :
    ResolutionLiftPrecomposition.kanTargetMap hcof hfib (𝟙 X)
        (ResolutionLiftPrecomposition.identity X) Z = 𝟙 _ :=
  ResolutionLiftPrecomposition.kanTargetMap_identity hcof hfib X Z

example {X Y W : ResolutionObject C} (f : X ⟶ Y) (g : Y ⟶ W)
    (φ : ResolutionLiftPrecomposition.FrameMap f) (ψ : ResolutionLiftPrecomposition.FrameMap g)
    (Z : C) :
    ResolutionLiftPrecomposition.kanTargetMap hcof hfib (f ≫ g)
        (ResolutionLiftPrecomposition.compose φ ψ) Z =
      ResolutionLiftPrecomposition.kanTargetMap hcof hfib g ψ Z ≫
        ResolutionLiftPrecomposition.kanTargetMap hcof hfib f φ Z :=
  ResolutionLiftPrecomposition.kanTargetMap_compose hcof hfib f g φ ψ Z

-- The actual Kan source map has the prescribed action on ordinary Ho(C),
-- with localization object and Hom universes independent of the source.
example {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] {X Y : ResolutionObject C} (f : X ⟶ Y)
    (Z : C) [IsFibrant Z] (z : SSet.π₀ (KanLiftAction.target hcof hfib Y Z)) :
    KanLiftAction.piZeroLocalizationEquiv hcof hfib Q X Z
        (SSet.mapπ₀ (ResolutionLiftPrecomposition.kanTargetMap hcof hfib f
          (ResolutionLiftPrecomposition.lift f) Z) z) =
      Q.map f.base ≫ KanLiftAction.piZeroLocalizationEquiv hcof hfib Q Y Z z :=
  ResolutionLiftPrecomposition.piZero_naturality_source hcof hfib Q f _ Z z

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.LiftSpacePrecomposition,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionLiftPrecomposition,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition]
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
  unless modules.size == expected.size do throwError "Some precomposition modules were not audited"
  logInfo m!"Lift precomposition audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
