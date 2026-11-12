module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.AnchoredFiniteFactorization
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.GluedPullbackTransport

/-!
概要：二つの全空間模型への相対有限射を、共通境界を保って同じ底の二 fiber へ移す。
方針：境界付き有限因子分解を貼り、その底の一つの収縮に沿って同時輸送する。
規約：元の引き戻し内の境界のホモトピーと、輸送後の厳密な境界式を保持する。
使われ方：積比較の単射性と相対境界の検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通境界を持つ二つの有限射は同じ底の fiber で厳密な相対射になる。
方針：元の境界を保つ二つの有限因子分解を pushout で貼り、同時に輸送する。
規約：境界射の単射性は不要。使われ方：積比較の相対有限検出。 -/
lemma continuousKanLeftFibration_pair_relative_detection {A K L E D B : SSet.{u}}
    [A.Finite] [K.Finite] [L.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (i : A ⟶ K) (j : A ⟶ L) (a : A ⟶ pullback p q)
    (f : K ⟶ continuousKanReplacement.obj E) (g : L ⟶ continuousKanReplacement.obj D)
    (hf : (a ≫ pullback.fst p q) ≫ continuousKanReplacementUnit.app E = i ≫ f)
    (hg : (a ≫ pullback.snd p q) ≫ continuousKanReplacementUnit.app D = j ≫ g) :
    ∃ b : B _⦋0⦌, ∃ s : A ⟶ vertexFiber p b, ∃ t : A ⟶ vertexFiber q b,
      ∃ r : K ⟶ continuousKanReplacement.obj (vertexFiber p b),
      ∃ v : L ⟶ continuousKanReplacement.obj (vertexFiber q b),
        i ≫ r = s ≫ continuousKanReplacementUnit.app (vertexFiber p b) ∧
        j ≫ v = t ≫ continuousKanReplacementUnit.app (vertexFiber q b) ∧
        Nonempty (SSet.Homotopy a (fiberPairToPullback p q b s t)) ∧
        Nonempty (SSet.Homotopy f (r ≫ continuousKanReplacement.map (vertexFiberι p b))) ∧
        Nonempty (SSet.Homotopy g (v ≫ continuousKanReplacement.map (vertexFiberι q b))) := by
  obtain ⟨k, a₀, r, ha₀, hr, hr'⟩ :=
    continuousKanReplacement_anchored_finite_factorization i (a ≫ pullback.fst p q) f hf
  obtain ⟨l, a₁, v, ha₁, hv, hv'⟩ :=
    continuousKanReplacement_anchored_finite_factorization j (a ≫ pullback.snd p q) g hg
  obtain ⟨b, s, t, Hs, Ht, Ha, _, _⟩ :=
    leftFibration_glued_pullback_transport p q a₀ a₁ k.val.ι l.val.ι a ha₀.symm ha₁.symm
  refine ⟨b, a₀ ≫ s, a₁ ≫ t, r ≫ continuousKanReplacement.map s,
    v ≫ continuousKanReplacement.map t, ?_, ?_, ⟨Ha⟩, ?_, ?_⟩
  · rw [← Category.assoc, hr, Category.assoc,
      ← continuousKanReplacementUnit.naturality, CategoryTheory.Functor.id_map]
    exact (Category.assoc _ _ _).symm
  · rw [← Category.assoc, hv, Category.assoc,
      ← continuousKanReplacementUnit.naturality, CategoryTheory.Functor.id_map]
    exact (Category.assoc _ _ _).symm
  · obtain ⟨H⟩ := continuousKanReplacement_map_homotopy Hs
    have H' := functorHomotopyPrecomp H r
    simpa only [CategoryTheory.Functor.map_comp, ← Category.assoc, hr'] using Nonempty.intro H'
  · obtain ⟨H⟩ := continuousKanReplacement_map_homotopy Ht
    have H' := functorHomotopyPrecomp H v
    simpa only [CategoryTheory.Functor.map_comp, ← Category.assoc, hv'] using Nonempty.intro H'

end SerrePositivity.InfinityCategories.F2
