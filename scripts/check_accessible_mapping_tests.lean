import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AccessibleModelMapping
import Lean.Util.CollectAxioms

noncomputable section
universe w t v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
  (resolutionHom)

variable {C : Type u} [Category.{v} C]

-- The diagram is arbitrary: neither a simplicial model structure nor
-- functoriality/accessibility in its source parameter is needed here.
example [IsAccessibleCategory.{w} C] {ι : Type t} [Small.{w} ι]
    (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C) [R.IsAccessible.{w}] (a : ι → C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      R.IsCardinalAccessible κ ∧
      (∀ i n, IsCardinalPresentable ((Q.obj (a i)).obj n) κ) ∧
      (∀ i, ((resolutionHom Q R).obj (op (a i))).IsCardinalAccessible κ) :=
  exists_accessible_resolutionHom_family Q R a

-- The detecting arrow really is precomposition, in the required direction.
example (F : Cᵒᵖ ⥤ C ⥤ SSet.{v}) (f : Arrow C) (Y : C) :
    ((MappingTests.arrow F f).obj Y).left = (F.obj (op f.right)).obj Y ∧
      ((MappingTests.arrow F f).obj Y).right = (F.obj (op f.left)).obj Y ∧
      ((MappingTests.arrow F f).obj Y).hom = (F.map f.hom.op).app Y :=
  ⟨rfl, rfl, rfl⟩

-- In particular the detecting map acts on actual simplices by Q(f)[n].
example (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C) (f : Arrow C)
    (Y : C) (n : SimplexCategoryᵒᵖ) (h : (Q.obj f.right).obj n.unop ⟶ R.obj Y) :
    (((MappingTests.arrow (resolutionHom Q R) f).obj Y).hom.app n) h =
      (Q.map f.hom).app n.unop ≫ h := rfl

variable [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- The final input is just the original combinatorial model and a small
-- arbitrary family of arrows, with no cofibrancy assumption on their ends.
-- The cardinal is shared with both actual model factorizations and original W.
example {ι : Type t} [Small.{w} ι] (s : ι → Arrow C) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      ∃ d : SerrePositivity.Smith.AccessibleModelFactorizations C κ,
        IsCardinalAccessibleCategory
          (SerrePositivity.Smith.arrowProperty (weakEquivalences C)).FullSubcategory κ ∧
        (SerrePositivity.Smith.arrowInclusion (weakEquivalences C)).IsCardinalAccessible κ ∧
        (∀ i, ((AccessibleModelMapping.hom d).obj (op (s i).left)).IsCardinalAccessible κ ∧
          ((AccessibleModelMapping.hom d).obj (op (s i).right)).IsCardinalAccessible κ) ∧
        (MappingTests.family (AccessibleModelMapping.hom d) s).IsCardinalAccessible κ :=
  exists_accessible_model_mapping_tests I J s

-- Empty localizing families are allowed; there is no implicit nonemptiness.
example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    ∃ d : SerrePositivity.Smith.AccessibleModelFactorizations C κ,
      (MappingTests.family (AccessibleModelMapping.hom d)
        (fun x : PEmpty.{1} ↦ x.elim)).IsCardinalAccessible κ := by
  obtain ⟨κ, hκ, d, _, _, _, h⟩ := exists_accessible_model_mapping_tests I J
    (fun x : PEmpty.{1} ↦ x.elim)
  exact ⟨κ, hκ, d, h⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Accessible,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AccessibleModelMapping]
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
  logInfo m!"Accessible mapping tests audit passed: {count} declarations in {seen.size} modules."
