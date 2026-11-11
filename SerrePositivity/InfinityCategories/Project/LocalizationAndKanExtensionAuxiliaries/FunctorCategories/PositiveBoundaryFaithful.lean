module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulBoundary
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FullSubcomplexMapping
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：正次元境界の全持ち上げによる充満忠実性の判定。
方針：頂点像の全部分複体へ因子化し、零次元の全射性を足して trivial Kan とする。
規約：元の射には頂点上の全射性を要求しない。
使われ方：Ind-S (4) の大きい標的に対する前合成の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 正次元の全境界を持ち上げる射は充満忠実。 -/
theorem isFullyFaithful_of_positive_boundary {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)
    (hp : ∀ n : ℕ, HasLiftingProperty (boundary (n + 1)).ι p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p := by
  let P : Y _⦋0⦌ → Prop := fun y => ∃ x, p.app (Opposite.op ⦋0⦌) x = y
  let B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y P
  let q : X ⟶ B.toSSet := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P p (fun x => ⟨x, rfl⟩)
  have hq : q ≫ B.ι = p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι P p _
  have hq0 : Function.Surjective (q.app (Opposite.op ⦋0⦌)) := by
    intro y
    obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y
    exact ⟨x, Subtype.ext hx⟩
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary q).2
    intro n
    cases n with
    | zero =>
      constructor
      intro a b sq
      obtain ⟨x, hx⟩ := hq0 (SSet.yonedaEquiv b)
      refine CommSq.HasLift.mk' {
        l := SSet.yonedaEquiv.symm x
        fac_left := boundary.hom_ext₀
        fac_right := ?_ }
      rw [SSet.yonedaEquiv_symm_comp, hx, Equiv.symm_apply_apply]
    | succ n =>
      have := hp n
      constructor
      intro a b sq
      have sq' : CommSq a (boundary (n + 1)).ι p (b ≫ B.ι) := by
        constructor
        rw [← hq, ← Category.assoc, sq.w, Category.assoc]
      refine CommSq.HasLift.mk' {
        l := sq'.lift
        fac_left := sq'.fac_left
        fac_right := ?_ }
      apply (cancel_mono B.ι).1
      rw [Category.assoc, hq]
      exact sq'.fac_right
  rw [← hq]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration q).isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι Y P)

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
