module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.FilteredLeftFibrationRelativeDetection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.ContinuousKanUnitHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-!
概要：全空間の Kan 模型での有限図式のホモトピーを同じ fiber で検出する。
方針：両端点を境界とする相対検出を円柱へ使い、fiber の単位を消去する。
規約：元の二図式へのホモトピーと fiber 内のホモトピーを同時に保持する。
使われ方：一般 coherent な filtered 図式の有限写像の同値関係の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：全空間模型でホモトピックな二つの有限図式は同じ fiber で比較できる。
方針：円柱と両端点を一つの fiber の置換へ移し、単位のホモトピー反映を使う。
規約：元の図式から fiber 内の二図式への実際のホモトピーも返す。 -/
lemma continuousKanLeftFibration_finite_homotopy_detection {K E B : SSet.{u}}
    [K.Finite] [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (f₀ f₁ : K ⟶ E)
    (H : SSet.Homotopy (f₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
      (f₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)) :
    ∃ b : B _⦋0⦌, ∃ g₀ g₁ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b,
      Nonempty (SSet.Homotopy f₀ (g₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) ∧
      Nonempty (SSet.Homotopy f₁ (g₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) ∧
      Nonempty (SSet.Homotopy g₀ g₁) := by
  let i : K ⨿ K ⟶ K ⊗ (Δ[1] : SSet.{u}) := coprod.desc SSet.ι₀ SSet.ι₁
  let a : K ⨿ K ⟶ E := coprod.desc f₀ f₁
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E = i ≫ H.h := by
    apply coprod.hom_ext
    · dsimp only [a, i]
      rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, coprod.inl_desc]
      exact H.h₀.symm
    · dsimp only [a, i]
      rw [← Category.assoc, coprod.inr_desc, ← Category.assoc, coprod.inr_desc]
      exact H.h₁.symm
  obtain ⟨b, t, g, hg, ⟨Ht⟩, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.continuousKanLeftFibration_finite_relative_detection p i a H.h ha
  let g₀ := (coprod.inl : K ⟶ K ⨿ K) ≫ t
  let g₁ := (coprod.inr : K ⟶ K ⨿ K) ≫ t
  refine ⟨b, g₀, g₁, ?_, ?_, ?_⟩
  · have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Ht (coprod.inl : K ⟶ K ⨿ K)
    simpa only [a, g₀, ← Category.assoc, coprod.inl_desc] using Nonempty.intro h
  · have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Ht (coprod.inr : K ⟶ K ⨿ K)
    simpa only [a, g₁, ← Category.assoc, coprod.inr_desc] using Nonempty.intro h
  · apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.continuousKanReplacementUnit_reflects_homotopy
    refine ⟨g, ?_, ?_, ?_⟩
    · change SSet.ι₀ ≫ g = g₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)
      have h := congrArg (fun q ↦ (coprod.inl : K ⟶ K ⨿ K) ≫ q) hg
      simpa only [i, g₀, ← Category.assoc, coprod.inl_desc] using h
    · change SSet.ι₁ ≫ g = g₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)
      have h := congrArg (fun q ↦ (coprod.inr : K ⟶ K ⨿ K) ≫ q) hg
      simpa only [i, g₁, ← Category.assoc, coprod.inr_desc] using h
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
