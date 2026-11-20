import SerrePositivity.HomotopicalAlgebra.Localization.Replacement
import SerrePositivity.HomotopicalAlgebra.Localization.ReplacementComparison
import SerrePositivity.HomotopicalAlgebra.Localization.ReplacementHomotopy
import SerrePositivity.HomotopicalAlgebra.Localization.ModelComparison
import SerrePositivity.HomotopicalAlgebra.Localization.Fibrations
import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vH uH
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Bousfield

variable {C : Type u} [Category.{v} C] [original : ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]


-- All local-replacement fields and accessibility are outputs of the final source contract.
example (S : MorphismProperty C) [S.IsSmall.{w}] :
    ∃ d : LocalReplacementData.{v, u} cof fib S, d.L.IsAccessible.{w} :=
  exists_accessible_localReplacementData cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S

example (S : MorphismProperty C) [S.IsSmall.{w}] :
    (localReplacementData cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S).L.IsAccessible.{w} :=
  localReplacementData_isAccessible cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S

variable {S T : MorphismProperty C} (d : LocalReplacementData.{v, u} cof fib S)
  (e : LocalReplacementData.{v, u} cof fib T)
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

example : localEquivalences.{v, u} (C := C) cof fib S =
    (weakEquivalences C).inverseImage d.L := d.detects_localEquivalences hcofV hfibV

example (X : C) : weakEquivalences C (d.η.app (d.L.obj X)) ∧
    weakEquivalences C (d.L.map (d.η.app X)) :=
  ⟨d.unit_at_value_weakEquivalence hcofV hfibV X, d.map_unit_weakEquivalence hcofV hfibV X⟩

-- The unit's universal property is a weak equivalence of the actual RMap simplicial sets.
example (X Z : C) (hZ : localObjects.{v, u} (C := C) cof fib S Z) :
    weakEquivalences SSet.{v}
      (((SerrePositivity.HomotopyFunctionComplex.chosenResolutionHom cof fib).map
        (d.η.app X).op).app Z) := d.unit_localEquivalence X Z hZ

example (X Z : C) (hZ : localObjects.{v, u} (C := C) cof fib S Z) :
    Function.Bijective (fun k : Q.obj (d.L.obj X) ⟶ Q.obj Z => Q.map (d.η.app X) ≫ k) :=
  d.unit_hom_bijective Q hcofV hfibV X Z hZ

example (X : C) : Q.map (d.L.map (d.η.app X)) = Q.map (d.η.app (d.L.obj X)) :=
  d.idempotence_coherence Q hcofV hfibV X

-- Both orders of nested replacement are compared to the stronger replacement.
example (h : S ≤ T) : e.L ⋙ Q ≅ (d.L ⋙ e.L) ⋙ Q :=
  d.compareRightLocalizationIso_of_le e hcofV hfibV Q h

example (h : S ≤ T) : e.L ⋙ Q ≅ (e.L ⋙ d.L) ⋙ Q :=
  e.compareLeftLocalizationIso_of_ge d hcofV hfibV Q h

example (e' : LocalReplacementData.{v, u} cof fib S) : d.L ⋙ Q ≅ e'.L ⋙ Q :=
  d.localizationIso hcofV hfibV Q e'

-- Generating-presentation independence compares the actual three model classes.
example {m n : ModelCategory C}
    (hm : @IsLocalizationModel C _ original _ cof fib S m)
    (hn : @IsLocalizationModel C _ original _ cof fib T n)
    (h : @localObjects C _ original _ cof fib S = @localObjects C _ original _ cof fib T) :
    m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations ∧
      m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithFibrations.fibrations = n.categoryWithFibrations.fibrations :=
  by
    let := original
    exact hm.classes_eq_of_localObjects_eq hn h

example {m n : ModelCategory C}
    (hm : @IsLocalizationModel C _ original _ cof fib S m)
    (hn : @IsLocalizationModel C _ original _ cof fib T n) (h : S ≤ T) :
    @SerrePositivity.Quillen.IsLeftQuillen C _ C _ m.categoryWithCofibrations
      m.categoryWithWeakEquivalences n.categoryWithCofibrations
      n.categoryWithWeakEquivalences (𝟭 C) := by
  let := original
  exact hm.identity_isLeftQuillen_to hn h


-- The replacement actually supplies fibrant replacement in the constructed model.
example (S : MorphismProperty C) [S.IsSmall.{w}] (X : C) :
    let p := modelPresentation cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S
    let d := localReplacementData cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S
    p.model.categoryWithCofibrations.cofibrations (d.η.app X) ∧
      p.model.categoryWithWeakEquivalences.weakEquivalences (d.η.app X) ∧
      p.model.categoryWithFibrations.fibrations (terminal.from (d.L.obj X)) := by
  let p := modelPresentation cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S
  let d := localReplacementData cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB S
  have h := p.isLocalizationModel cof fib I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB
  exact ⟨(h.replacement_unit_trivialCofibration d X).1,
    (h.replacement_unit_trivialCofibration d X).2, h.replacement_value_fibrant d X⟩

example {m : ModelCategory C} (h : @IsLocalizationModel C _ original _ cof fib S m)
    {X Y : C} (f : X ⟶ Y) (hX : @localObjects C _ original _ cof fib S X)
    (hY : @localFibrantObjects C _ original _ cof fib S Y) :
    m.categoryWithFibrations.fibrations f ↔ original.categoryWithFibrations.fibrations f := by
  let := original
  exact h.fibration_iff_of_local hcofV hfibV f hX hY

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Localization.ReplacementData,
    `SerrePositivity.HomotopicalAlgebra.Localization.Replacement,
    `SerrePositivity.HomotopicalAlgebra.Localization.ReplacementComparison,
    `SerrePositivity.HomotopicalAlgebra.Localization.ReplacementHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Localization.ModelComparison,
    `SerrePositivity.HomotopicalAlgebra.Localization.Fibrations]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Local replacement and comparison audit passed: {count} declarations in {seen.size} modules."
