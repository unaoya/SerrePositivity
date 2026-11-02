module

public import SerrePositivity.InfinityCategories.F1.FilteredExchange.AnchoredFiniteFactorization
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanRelativeReflection

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
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 指定点を持つ有限境界の定数性は、fiber への有限検出と置換の除去で保たれる。 -/
lemma finite_constant_boundary_fiber_detection {A K E B : SSet.{u}}
    [A.Finite] [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (i : A ⟶ K)
    (q : A ⟶ (Δ[0] : SSet.{u})) (z : (Δ[0] : SSet.{u}) ⟶ A)
    (hz : z ≫ q = 𝟙 _) (x : (Δ[0] : SSet.{u}) ⟶ E)
    (f : K ⟶ continuousKanReplacement.obj E)
    (hf : (q ≫ x) ≫ continuousKanReplacementUnit.app E = i ≫ f) :
    ∃ b : B _⦋0⦌, ∃ y : (Δ[0] : SSet.{u}) ⟶ vertexFiber p b,
      ∃ g : K ⟶ vertexFiber p b,
        i ≫ g = q ≫ y ∧
        Nonempty (SSet.Homotopy x (y ≫ vertexFiberι p b)) ∧
        Nonempty (SSet.Homotopy f
          (g ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E)) := by
  obtain ⟨k, a, r, ha, hr, hrf⟩ :=
    continuousKanReplacement_anchored_finite_factorization i (q ≫ x) f hf
  have hconst : a = q ≫ z ≫ a := by
    apply (cancel_mono k.val.ι).mp
    rw [ha, Category.assoc, Category.assoc, ha, ← Category.assoc z q x, hz,
      Category.id_comp]
  obtain ⟨b, s, ⟨Hs⟩⟩ := leftFibration_finite_fiber_detection p k.val.ι
  let y := z ≫ a ≫ s
  have hb : i ≫ (r ≫ continuousKanReplacement.map s) =
      (q ≫ y) ≫ continuousKanReplacementUnit.app (vertexFiber p b) := by
    rw [← Category.assoc, hr, Category.assoc,
      ← continuousKanReplacementUnit.naturality, Functor.id_map]
    change a ≫ s ≫ continuousKanReplacementUnit.app (vertexFiber p b) = _
    rw [hconst]
    simp only [y, Category.assoc]
  obtain ⟨g, hg, G, _⟩ := continuousKanReplacement_relative_reflection i (q ≫ y)
    (r ≫ continuousKanReplacement.map s) hb
  refine ⟨b, y, g, hg, ?_, ?_⟩
  · have H := functorHomotopyPrecomp Hs (z ≫ a)
    have hx : (z ≫ a) ≫ k.val.ι = x := by
      rw [Category.assoc, ha, ← Category.assoc, hz, Category.id_comp]
    simpa only [hx, y, Category.assoc] using Nonempty.intro H
  · obtain ⟨Ht⟩ := continuousKanReplacement_map_homotopy Hs
    have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
      (Nonempty.intro (functorHomotopyPrecomp Ht r))
    have h₂ := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
      (Nonempty.intro (functorHomotopyPostcomp G
        (continuousKanReplacement.map (vertexFiberι p b))))
    simp only [Functor.map_comp, Category.assoc] at h₁ h₂
    apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
    simpa only [Functor.map_comp, ← Category.assoc, hrf,
      ← continuousKanReplacementUnit.naturality, Functor.id_map] using h₁.trans h₂.symm

end SerrePositivity.InfinityCategories.F2.PiCriterion
