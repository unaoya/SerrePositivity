import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u w
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Model-independent gluing, with the cover index universe independent of v.
example {X P : SSet.{v}} {I : Type w} (A : X.Subcomplex) (U : I → X.Subcomplex)
    (hU : ⨆ i, U i = A) (f : ∀ i, (U i).toSSet ⟶ P)
    (hf : ∀ i j, SSet.Subcomplex.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      SSet.Subcomplex.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    ∃ e : A.toSSet ⟶ P,
      ∀ i, SSet.Subcomplex.homOfLE (show U i ≤ A from hU ▸ le_iSup U i) ≫ e = f i :=
  ⟨SubcomplexGluing.desc A U hU f hf, SubcomplexGluing.desc_fac A U hU f hf⟩

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Prescribed standard faces are retained after evaluation as whole families,
-- while the original fixed boundary stays fixed throughout the filler.
example {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (n : ℕ)
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶
      RelativeChoiceSpace.obj i b)) (hf : BoundaryGluing.StandardCompatible f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ⟶ RelativeChoiceSpace.obj i b,
      (∀ k, T ◁ SSet.stdSimplex.δ k ≫ RelativeChoiceSpace.family i b e =
        RelativeChoiceSpace.family i b (f k)) ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ≫ RelativeChoiceSpace.family i b e =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
          (ρ_ V).hom ≫ b := by
  obtain ⟨e, he, hb⟩ := RelativeChoiceSpace.fill_standard_faces hcof hfib i b p hp n f hf
  refine ⟨e, fun k => ?_, hb⟩
  rw [← RelativeChoiceSpace.family_naturality, he k]

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- All dimensions, including zero, from compatible maps on actual facets.
-- A whole boundary map is constructed rather than supplied as an input.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (n : ℕ)
    (a : ∀ k, (BoundaryGluing.facet n k).toSSet ⟶ CoherentLiftRelative.postChoiceSpace X Y W f g)
    (ha : BoundaryGluing.Compatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
        CoherentLiftRelative.postChoiceSpace X Y W f g,
      ∀ k, (BoundaryGluing.facet n k).ι ≫ e = a k := by
  obtain ⟨e, he, _⟩ := CoherentLiftRelative.post_fill_faces hcof hfib X Y W f g n a ha
  exact ⟨e, he⟩

example (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (n : ℕ)
    (a : ∀ k, (BoundaryGluing.facet n k).toSSet ⟶ CoherentLiftRelative.preChoiceSpace X Y W f g)
    (ha : BoundaryGluing.Compatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
        CoherentLiftRelative.preChoiceSpace X Y W f g,
      ∀ k, (BoundaryGluing.facet n k).ι ≫ e = a k := by
  obtain ⟨e, he, _⟩ := CoherentLiftRelative.pre_fill_faces hcof hfib X Y W f g n a ha
  exact ⟨e, he⟩

-- A prescribed triangle of relative comparison edges is filled. Its actual
-- Kan action restricts to each of the three prescribed edge actions, for
-- every Z and parameter t, using the same filler chosen before Z and t.
example (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W)
    (a : Fin 3 → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶
      CoherentLiftRelative.postChoiceSpace X Y W f g)) (ha : BoundaryGluing.StandardCompatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
        CoherentLiftRelative.postChoiceSpace X Y W f g,
      ∀ (Z : C) (t : CoherentLiftTuples.obj X Y f ⊗
          SSet.stdSimplex.{v}.obj (SimplexCategory.mk 2) ⟶
            (cosimplicialHom W.resolution.obj).obj Z) (k : Fin 3),
        CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k ≫
            KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
              (RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X Y f)
                (CoherentLiftRelative.postBoundary X Y W f g) e) t =
          KanLiftAction.parameterized hcof hfib X W (f ≫ g.base) Z
            (RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X Y f)
              (CoherentLiftRelative.postBoundary X Y W f g) (a k))
            ((CoherentLiftTuples.obj X Y f ◁ SSet.stdSimplex.δ k) ≫ t) := by
  obtain ⟨e, he, _⟩ := RelativeChoiceSpace.fill_standard_faces hcof hfib
    (CoherentLiftRelative.vertexInclusion X Y f) (CoherentLiftRelative.postBoundary X Y W f g)
    (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base)) 0 a ha
  refine ⟨e, fun Z t k => ?_⟩
  rw [KanLiftAction.parameterized_naturality, ← RelativeChoiceSpace.family_naturality, he k]

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceBoundary,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftFaces]
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
  unless modules.size == expected.size do throwError "Some prescribed face modules were not audited"
  logInfo m!"Coherent lift face audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
