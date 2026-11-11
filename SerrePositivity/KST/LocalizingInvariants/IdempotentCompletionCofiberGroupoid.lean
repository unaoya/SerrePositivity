module

public import SerrePositivity.KST.LocalizingInvariants.CompletionWideContraction
public import SerrePositivity.KST.Spectra.ComponentRetractionKanHomotopy

/-!
概要：安定 ∞ 圏の冪等完備化の元の本質像による分母亜群化は離散である。
方針：全辺条件の wide 部分複体を、密度から得た零分母で離散成分へ収縮する。
規約：元の本質像と全単体条件を保持し、SConstruction を import しない。
使われ方：K-cof の各 S 多次数の wide 部分複体の供給。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 概要：元の本質像の cofiber 分母の全辺 wide 部分複体は、離散な亜群化を持つ。
方針：全辺条件の wide 部分複体を、密度から得た零分母で離散成分へ収縮する。
規約：元の本質像と全単体条件を保持し、SConstruction を import しない。
使われ方：K-cof の各 S 多次数の wide 部分複体の供給。 -/
theorem idempotentCompletion_cofiberWide_discrete
    (C D : SSet.{u}) [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
    (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) :
    ∃ M : D.Subcomplex,
      (∀ (n : ℕ) (s : D _⦋n⦌), s ∈ M.obj (Opposite.op ⦋n⦌) ↔
        ∀ θ : ⦋1⦌ ⟶ ⦋n⦌, D.map θ.op s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
          {y | ∃ x : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x) y)}) ∧
      Quasicategory (M : SSet.{u}) ∧
      ∀ (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (M : SSet.{u})) _⦋0⦌) (n : ℕ),
        0 < n → Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (M : SSet.{u})) n x) := by
  refine ⟨completionCofiberWide f, ?_, completionCofiberWide_quasicategory f h, ?_⟩
  · intro n s
    exact Iff.rfl
  · intro x n hn
    exact Spectra.continuousKanReplacement_positive_subsingleton_of_componentRetraction
      (completionComponentProjection f) (completionComponentSection f h)
      (completionComponentSection_projection f h) (completionWideContraction f h) x n hn

end SerrePositivity.KST.LocalizingInvariants
