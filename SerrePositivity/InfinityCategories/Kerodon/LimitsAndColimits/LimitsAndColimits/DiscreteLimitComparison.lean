module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexInvertingLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.DiagramPathSpan
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
概要：離散図式の実際の極限は、quasicategory の成分ごとの同値を保つ。
方針：内ホーンを各成分で充填し、可逆 path 置換の両射影の積を取る。
規約：等化子など任意の厳密極限に対する同値不変性は主張しない。
使われ方：小余積の底上での局所化比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- quasicategory の離散図式の任意の極限錐の頂点も quasicategory。 -/
lemma quasicategory_of_discrete_limit {I : Type u} (F : Discrete I ⥤ SSet.{u})
    (c : Cone F) (hc : IsLimit c) [∀ j, Quasicategory (F.obj j)] : Quasicategory c.pt where
  hornFilling' {n i} a h₀ hn := by
    have hf (j : Discrete I) := Quasicategory.hornFilling' (a ≫ c.π.app j) h₀ hn
    let s : Cone F := {
      pt := Δ[n + 2]
      π := Discrete.natTrans (fun j ↦ (hf j).choose) }
    refine ⟨hc.lift s, ?_⟩
    apply hc.hom_ext
    intro j
    rw [Category.assoc, hc.fac]
    exact (hf j).choose_spec

/-- 離散図式の成分ごとの trivial Kan fibration は、極限の比較でも同じ性質を持つ。 -/
lemma trivialKanFibration_limMap_discrete {I : Type u}
    {F G : Discrete I ⥤ SSet.{u}} (η : F ⟶ G)
    [∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (η.app j)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (limMap η) := by
  constructor
  change (MorphismProperty.monomorphisms SSet.{u}).rlp (limMap η)
  exact (MorphismProperty.monomorphisms SSet.{u}).rlp.limMap η
    (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := η.app j))

/-- 成分ごとの同値は、離散図式の実際の極限の比較を前合成同値にする。 -/
lemma isPrecompositionEquivalence_limMap_discrete {I : Type u}
    {F G : Discrete I ⥤ SSet.{u}} [∀ j, Quasicategory (F.obj j)]
    [∀ j, Quasicategory (G.obj j)] (η : F ⟶ G)
    (hη : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app j)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (limMap η) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathReplacement η
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathProjection η
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathEndpoint η
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection η
  have : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (p.app j) := by
    intro j
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (η.app j))
    infer_instance
  have : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (q.app j) := fun j ↦
    (hη j).equivalencePathReplacementMap_trivialKanFibration
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (limMap p) := trivialKanFibration_limMap_discrete p
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (limMap q) := trivialKanFibration_limMap_discrete q
  have : ∀ j, Quasicategory (R.obj j) := by
    intro j
    change Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (η.app j))
    infer_instance
  have : Quasicategory (limit F) := quasicategory_of_discrete_limit F _ (limit.isLimit F)
  have : Quasicategory (limit G) := quasicategory_of_discrete_limit G _ (limit.isLimit G)
  have : Quasicategory (limit R) := quasicategory_of_discrete_limit R _ (limit.isLimit R)
  have hsp : limMap s ≫ limMap p = 𝟙 (limit F) := by
    change lim.map s ≫ lim.map p = 𝟙 _
    rw [← lim.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection_projection, lim.map_id]
  have hsq : limMap s ≫ limMap q = limMap η := by
    change lim.map s ≫ lim.map q = lim.map η
    rw [← lim.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.diagramPathSection_endpoint]
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (limMap s) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (limMap p)).cancel_right
    rw [hsp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl _).isQCatEquivalence
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (limMap η) := by
    rw [← hsq]
    exact hs.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (limMap q))
  exact he.isPrecompositionEquivalence

/-- 離散図式の任意の二つの極限錐でも、成分ごとの同値は実際の比較を同値にする。 -/
lemma isPrecompositionEquivalence_discreteConeMap {I : Type u}
    {F G : Discrete I ⥤ SSet.{u}} [∀ j, Quasicategory (F.obj j)]
    [∀ j, Quasicategory (G.obj j)] (η : F ⟶ G)
    (hη : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (η.app j)) (c : Cone F) (d : Cone G)
    (hc : IsLimit c) (hd : IsLimit d) (φ : c.pt ⟶ d.pt)
    (hφ : ∀ j, φ ≫ d.π.app j = c.π.app j ≫ η.app j) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence φ := by
  let ec := hc.conePointUniqueUpToIso (limit.isLimit F)
  let ed := hd.conePointUniqueUpToIso (limit.isLimit G)
  have he : φ ≫ ed.hom = ec.hom ≫ limMap η := by
    apply limit.hom_ext
    intro j
    dsimp only [ec, ed]
    rw [Category.assoc, limit.conePointUniqueUpToIso_hom_comp, Category.assoc,
      limMap_π, ← Category.assoc, limit.conePointUniqueUpToIso_hom_comp]
    exact hφ j
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso ed).cancel_right
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso ec).comp
    (isPrecompositionEquivalence_limMap_discrete η hη)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
