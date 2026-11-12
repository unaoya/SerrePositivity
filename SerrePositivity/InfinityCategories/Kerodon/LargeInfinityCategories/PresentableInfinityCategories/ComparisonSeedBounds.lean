module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonInitialExistence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCosliceEdge
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
概要：元の二つの小さい種集合を支配する、実際の初期全比較を選ぶ。
方針：filtered poset 内の上界と、点 coslice が保持する元の順序射を使う。
規約：種集合も元の二表示の添字も変更しない。使われ方：可算部分表示の開始条件。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- poset の点 coslice の頂点は、元の同じ poset の開始点の後にある。 -/
lemma nerve_pointCoslice_le {A : Type u} [Preorder A] (a : A)
    (j : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder ((SSet.yonedaEquiv (X := nerve A)).symm (nerveEquiv.symm a))) _⦋0⦌) :
    a ≤ nerveEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := (SSet.yonedaEquiv (X := nerve A)).symm (nerveEquiv.symm a)) j) := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge ((SSet.yonedaEquiv (X := nerve A)).symm (nerveEquiv.symm a)) j
  let e : (nerve A).Edge (nerveEquiv.symm a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := (SSet.yonedaEquiv (X := nerve A)).symm (nerveEquiv.symm a)) j) :=
    ⟨t.edge, t.src_eq.trans (Equiv.apply_symm_apply _ _), t.tgt_eq⟩
  simpa only [Equiv.apply_symm_apply] using leOfHom (CategoryTheory.nerve.homEquiv e)

/-- 両側の種集合を支配する開始点を、同じ元の二表示の初期比較内で選べる。 -/
lemma exists_seedBoundedComparison {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C] {A₀ A₁ : Type u}
    [Preorder A₀] [Preorder A₁] [IsCardinalFiltered A₀ κ] [IsCardinalFiltered A₁ κ]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve A₁)]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C)
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁) (hc₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c₁)
    (hv : c₀.vertex = c₁.vertex)
    (hD₀ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₀.app _ (ULift.up j)))
    (hD₁ : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₁.app _ (ULift.up j)))
    (seed₀ : Set A₀) (hs₀ : HasCardinalLT seed₀ κ)
    (seed₁ : Set A₁) (hs₁ : HasCardinalLT seed₁ κ) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison κ D₀ D₁ c₀ c₁,
      (∀ a ∈ seed₀, a ≤ nerveEquiv (s.left_index.app _ s.left_terminal)) ∧
      (∀ b ∈ seed₁, b ≤ nerveEquiv (s.right_index.app _ s.right_terminal)) := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialSeed_bound seed₀ hs₀
  obtain ⟨b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_sequentialSeed_bound seed₁ hs₁
  obtain ⟨s, hleft, j, hright⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_comparisonInitialState D₀ D₁ c₀ c₁ hc₁ hv
    (nerveEquiv.symm a) (nerveEquiv.symm b) (hD₀ _) hD₁
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    rw [hleft, Equiv.apply_symm_apply]
    exact ha x hx
  · intro y hy
    rw [hright]
    exact (hb y hy).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerve_pointCoslice_le b j)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
