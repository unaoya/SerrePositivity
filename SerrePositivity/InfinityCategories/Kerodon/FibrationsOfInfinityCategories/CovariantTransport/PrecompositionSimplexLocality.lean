module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverCellularNaturalComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackMorphism
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：底の各標準単体への pullback による前合成の同値条件の判定。
方針：pullback を底上の対象に関する自然な比較とし、セル分解で全体へ拡張する。
規約：底や比較の始域・終域に quasicategory 性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体を終域とする円柱比較から一般の終域への還元。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：初期な底への pullback で得られる比較は同値条件を満たす。
方針：両 pullback 関手が初期対象を保つことから、二つの初期対象の同型として比較する。
規約：元の底上の射に追加条件はない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、局所的な比較判定の初期部分。 -/
lemma isPrecompositionEquivalence_overPullbackMap_initial
    {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap u (⊥_ (Over S))) := by
  have hA : IsInitial ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying a.hom).obj (⊥_ (Over S))) :=
    IsInitial.isInitialObj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying a.hom) _ initialIsInitial
  have hB : IsInitial ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying b.hom).obj (⊥_ (Over S))) :=
    IsInitial.isInitialObj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying b.hom) _ initialIsInitial
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap u (⊥_ (Over S)) = (hA.uniqueUpToIso hB).hom := hA.hom_ext _ _
  rw [he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso _

/-- 概要：底の全ての標準単体上で pullback の比較が同値条件を満たせば元の比較も満たす。
方針：Over 圏のセルによる自然な比較の判定を使い、恒等な底への pullback を元の射と同定する。
規約：各標準単体への射は退化したものも全て含む。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、円柱比較の一般の終域への還元。 -/
lemma isPrecompositionEquivalence_of_pullback_stdSimplex
    {S : SSet.{u}} {a b : Over S} (u : a ⟶ b)
    (hstd : ∀ (n : ℕ) (p : (Δ[n] : SSet.{u}) ⟶ S),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap u (Over.mk p))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence u.left := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_over_natComponent_of_stdSimplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat u) (isPrecompositionEquivalence_overPullbackMap_initial u) hstd S (𝟙 S)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap u (Over.mk (𝟙 S))) at h
  let eA := asIso (pullback.snd (𝟙 S) a.hom)
  let eB := asIso (pullback.snd (𝟙 S) b.hom)
  have hc := h.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso eB)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap u (Over.mk (𝟙 S)) ≫ pullback.snd (𝟙 S) b.hom) at hc
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap_snd u (Over.mk (𝟙 S))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap u (Over.mk (𝟙 S)) ≫ pullback.snd (𝟙 S) b.hom =
    pullback.snd (𝟙 S) a.hom ≫ u.left at he
  rw [he] at hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso eA).cancel_left hc

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
