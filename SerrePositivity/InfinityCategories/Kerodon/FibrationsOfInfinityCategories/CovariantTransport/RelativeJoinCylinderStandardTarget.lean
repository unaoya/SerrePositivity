module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderSkeletonColimit
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLastFaceFactor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPoint

/-!
概要：標準単体を終域とする任意の射の写像円柱比較の同値条件。
方針：終域の次元の帰納の内側で始域の骨格の次元を帰納し、境界とセルを同時に処理する。
規約：始域の有限性や quasicategory 性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、一般の終域への局所的な還元の入力。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：標準単体を終域とする全ての射の写像円柱比較は前合成の同値条件を満たす。
方針：終域の帰納の中で全ての骨格を帰納し、最後の頂点を保つ場合の境界と保たない場合の右錐を使う。
規約：始域 X は任意の単体集合。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域の各単体への制限の比較。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_standardTarget (n : ℕ) :
    ∀ {X : SSet.{u}} (f : X ⟶ Δ[n]),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f) := by
  induction n with
  | zero =>
    intro X f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_point f
  | succ n ih =>
    have hsk : ∀ d (X : SSet.{u}) (f : X ⟶ Δ[n + 1]),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison ((skeletonOfMono (initial.to X) d).ι ≫ f)) := by
      intro d
      induction d with
      | zero =>
        intro X f
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_sourceIso_iff
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBaseZeroIso (initial.to X)).symm
          ((skeletonOfMono (initial.to X) 0).ι ≫ f)).mp
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_isInitialSource
          _ initialIsInitial
      | succ d hd =>
        intro X f
        have hb : ∀ g : (boundary d : SSet.{u}) ⟶ Δ[n + 1],
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison g) := by
          intro g
          exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_sourceIso_iff
            (asIso (skeletonOfMono (initial.to (boundary d : SSet.{u})) d).ι) g).mp
              (hd (boundary d : SSet.{u}) g)
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_skeleton_succ
          (initial.to X) f d (hd X f)
        · intro c
          exact hb _
        · intro c
          exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_stdSimplex_step
            (c.map ≫ f) (fun g ↦ ih g) (hb _)
    intro X f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_of_skeletons
      (initial.to X) f (fun d ↦ hsk d X f)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
