module
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredLeftFibrationTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanHomotopy

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.AnchoredFiniteFactorization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanRelativeReflection

/-!
概要：有限な定数境界付きの射を、定数境界のまま一つの実際の Kan fiber へ移す。
方針：有限台の包含の単射性で境界の定数性を保ち、強変形 retract で置換を除く。
規約：境界の指定点を保持する。単なる非相対の有限値検出からは推論しない。
使われ方：境界定数単体による正次数 π の代表元検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 指定点を持つ有限境界の定数性は、fiber への有限検出と置換の除去で保たれる。 -/
lemma finite_constant_boundary_fiber_detection {A K E B : SSet.{u}}
    [A.Finite] [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : A ⟶ K)
    (q : A ⟶ (Δ[0] : SSet.{u})) (z : (Δ[0] : SSet.{u}) ⟶ A)
    (hz : z ≫ q = 𝟙 _) (x : (Δ[0] : SSet.{u}) ⟶ E)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E)
    (hf : (q ≫ x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E = i ≫ f) :
    ∃ b : B _⦋0⦌, ∃ y : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b,
      ∃ g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b,
        i ≫ g = q ≫ y ∧
        Nonempty (SSet.Homotopy x (y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) ∧
        Nonempty (SSet.Homotopy f
          (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)) := by
  obtain ⟨k, a, r, ha, hr, hrf⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_anchored_finite_factorization i (q ≫ x) f hf
  have hconst : a = q ≫ z ≫ a := by
    apply (cancel_mono k.val.ι).mp
    rw [ha, Category.assoc, Category.assoc, ha, ← Category.assoc z q x, hz,
      Category.id_comp]
  obtain ⟨b, s, ⟨Hs⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.leftFibration_finite_fiber_detection p k.val.ι
  let y := z ≫ a ≫ s
  have hb : i ≫ (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map s) =
      (q ≫ y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := by
    rw [← Category.assoc, hr, Category.assoc,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map]
    change a ≫ s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) = _
    rw [hconst]
    simp only [y, Category.assoc]
  obtain ⟨g, hg, G, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_relative_reflection i (q ≫ y)
    (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map s) hb
  refine ⟨b, y, g, hg, ?_, ?_⟩
  · have H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hs (z ≫ a)
    have hx : (z ≫ a) ≫ k.val.ι = x := by
      rw [Category.assoc, ha, ← Category.assoc, hz, Category.id_comp]
    simpa only [hx, y, Category.assoc] using Nonempty.intro H
  · obtain ⟨Ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_map_homotopy Hs
    have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
      (Nonempty.intro (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Ht r))
    have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
      (Nonempty.intro (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp G
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))))
    simp only [Functor.map_comp, Category.assoc] at h₁ h₂
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
    simpa only [Functor.map_comp, ← Category.assoc, hrf,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality, Functor.id_map] using h₁.trans h₂.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
