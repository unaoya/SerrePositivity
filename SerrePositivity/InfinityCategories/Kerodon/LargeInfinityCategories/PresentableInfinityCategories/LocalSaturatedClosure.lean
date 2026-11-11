module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.StronglySaturatedClosure

/-!
概要：強飽和生成閉包は、元の局所対象と局所同値を変えない。
方針：元の辺集合と局所同値の間に生成閉包を挟み、局所性の反変性を使う。
規約：添字 u の全小余極限だけを要求。局所同値と生成閉包の一致は主張しない。
使われ方：HTT 5.5.4 の小生成と局所化の存在の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {X : SSet.{max u v}} [Quasicategory X]

/-- 小余極限のある圏で、元の強飽和生成閉包の全ての辺は元の局所同値。 -/
lemma stronglySaturatedClosure_subset_localEquivalences (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj W ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure_minimal _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_stronglySaturated W hX)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.subset_localEquivalences W)

/-- 強飽和生成閉包への拡大は、元の局所対象を変えない。 -/
lemma isLocalObject_stronglySaturatedClosure_iff (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj W) z ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject W z := by
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalObject_of_subset (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.subset_stronglySaturatedClosure _ W)
  · intro hz
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalObject_of_subset (stronglySaturatedClosure_subset_localEquivalences W hX)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isLocalObject_localEquivalences_iff W z).mpr hz)

/-- 強飽和生成閉包への拡大は、全局所対象で検出する元の局所同値を変えない。 -/
lemma localEquivalences_stronglySaturatedClosure (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj W) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  apply Set.Subset.antisymm
  · have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences_mono (stronglySaturatedClosure_subset_localEquivalences W hX)
    rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences_idempotent] at h
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.subset_stronglySaturatedClosure _ W)

/-- 強飽和生成閉包は元の局所対象の全部分 quasicategory 自体を保持。 -/
lemma localObjectsSubcomplex_stronglySaturatedClosure (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.stronglySaturatedClosure (SSet.uliftFunctor.{v, u}).obj W) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex W := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex
  congr 1
  funext z
  exact propext (isLocalObject_stronglySaturatedClosure_iff W hX z)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
