module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimultaneousRelativeDetection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CylinderUnitReflection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberPairHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-!
概要：積比較の二つの成分でホモトピックな有限射を、同じ二 fiber の積で比較する。
方針：両端点を共通境界として同時検出し、二つの円柱を fiber 内で反映して組み合わせる。
規約：元の二射の輸送は引き戻し内のホモトピーで保持する。
使われ方：積比較の有限写像空間の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：二成分が置換内でホモトピックな有限二射は、共通 fiber の積で比較できる。
方針：二つの円柱に境界付き同時検出を使い、fiber の単位のホモトピー反映で戻す。
規約：元の引き戻しを変更しない。使われ方：積比較の単射側の検出。 -/
lemma totalKanProductComparison_finite_homotopy_detection {K E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (a₀ a₁ : K ⟶ pullback p q)
    (H : SSet.Homotopy (a₀ ≫ pullback.fst p q ≫ continuousKanReplacementUnit.app E)
      (a₁ ≫ pullback.fst p q ≫ continuousKanReplacementUnit.app E))
    (G : SSet.Homotopy (a₀ ≫ pullback.snd p q ≫ continuousKanReplacementUnit.app D)
      (a₁ ≫ pullback.snd p q ≫ continuousKanReplacementUnit.app D)) :
    ∃ c₀ c₁ : K ⟶ pullback p q,
      Nonempty (SSet.Homotopy a₀ c₀) ∧ Nonempty (SSet.Homotopy a₁ c₁) ∧
      Nonempty (SSet.Homotopy c₀ c₁) := by
  let i : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) := coprod.desc SSet.ι₀ SSet.ι₁
  let a : K ⨿ K ⟶ pullback p q := coprod.desc a₀ a₁
  have endpoint {X : SSet.{u}} (v : pullback p q ⟶ X)
      (h : SSet.Homotopy (a₀ ≫ v ≫ continuousKanReplacementUnit.app X)
        (a₁ ≫ v ≫ continuousKanReplacementUnit.app X)) :
      (a ≫ v) ≫ continuousKanReplacementUnit.app X = i ≫ h.h := by
    apply coprod.hom_ext
    · dsimp only [a, i]
      rw [← Category.assoc, ← Category.assoc, coprod.inl_desc,
        ← Category.assoc, coprod.inl_desc]
      exact h.h₀.symm
    · dsimp only [a, i]
      rw [← Category.assoc, ← Category.assoc, coprod.inr_desc,
        ← Category.assoc, coprod.inr_desc]
      exact h.h₁.symm
  obtain ⟨b, s, t, r, v, hr, hv, ⟨Ha⟩, _, _⟩ :=
    continuousKanLeftFibration_pair_relative_detection p q i i a H.h G.h
      (endpoint (pullback.fst p q) H) (endpoint (pullback.snd p q) G)
  obtain ⟨Hs⟩ := continuousKanReplacementUnit_reflects_cylinder s r hr
  obtain ⟨Ht⟩ := continuousKanReplacementUnit_reflects_cylinder t v hv
  let c₀ := fiberPairToPullback p q b ((coprod.inl : K ⟶ K ⨿ K) ≫ s)
    ((coprod.inl : K ⟶ K ⨿ K) ≫ t)
  let c₁ := fiberPairToPullback p q b ((coprod.inr : K ⟶ K ⨿ K) ≫ s)
    ((coprod.inr : K ⟶ K ⨿ K) ≫ t)
  refine ⟨c₀, c₁, ?_, ?_, ⟨fiberPairHomotopy p q b Hs Ht⟩⟩
  · have h := functorHomotopyPrecomp Ha (coprod.inl : K ⟶ K ⨿ K)
    have he : (coprod.inl : K ⟶ K ⨿ K) ≫ fiberPairToPullback p q b s t = c₀ := by
      apply pullback.hom_ext <;>
        simp only [c₀, fiberPairToPullback, Category.assoc, pullback.lift_fst, pullback.lift_snd]
    simpa only [a, coprod.inl_desc, he] using Nonempty.intro h
  · have h := functorHomotopyPrecomp Ha (coprod.inr : K ⟶ K ⨿ K)
    have he : (coprod.inr : K ⟶ K ⨿ K) ≫ fiberPairToPullback p q b s t = c₁ := by
      apply pullback.hom_ext <;>
        simp only [c₁, fiberPairToPullback, Category.assoc, pullback.lift_fst, pullback.lift_snd]
    simpa only [a, coprod.inr_desc, he] using Nonempty.intro h

end SerrePositivity.InfinityCategories.F2
