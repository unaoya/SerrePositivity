module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonSequenceSliceDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CoconeSliceDiagram

/-!
概要：元の両表示余錐を同じ大域頂点の slice 内で比較する。
方針：公開 P の余錐 slice 表示を等しい頂点間で移し、全 uncurry の単射性を使う。
規約：両側の元の全余錐を保持する。使われ方：共通全比較の部分列との厳密な一致。

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


/-- 指定余錐の slice 表示を、等しい指定大域頂点の slice へ移す。 -/
def transportedCoconeSliceDiagram {K C : SSet.{u}} {D : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (z : C _⦋0⦌) (h : c.vertex = z) :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c ≫
    (eqToIso (congrArg (fun y ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm y)) h)).hom

/-- 大域頂点の等号による移送は元の全余錐値を保持する。 -/
lemma transportedCoconeSliceDiagram_uncurry {K C : SSet.{u}} {D : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (z : C _⦋0⦌) (h : c.vertex = z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (transportedCoconeSliceDiagram c z h) = c.val := by
  cases h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram_uncurry c

/-- 同じ移送の後でも、元の全底図式が射影で回収される。 -/
lemma transportedCoconeSliceDiagram_projection {K C : SSet.{u}} {D : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (z : C _⦋0⦌) (h : c.vertex = z) :
    transportedCoconeSliceDiagram c z h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z) = D := by
  cases h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram_projection c

variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}

/-- 左側の元の全余錐は、同じ大域頂点上の全比較図式に厳密に含まれる。 -/
lemma comparisonSliceDiagram_left (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    (SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram s =
      (SSet.uliftFunctor.{u + 1, u}).map s.left_index ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram c₀ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (SSet.yonedaEquiv.symm c₀.vertex)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coconeSliceDiagram_uncurry]
  exact s.left_augmentation

/-- 右側についても、元の同じ大域頂点上へ移した全余錐を厳密に回収する。 -/
lemma comparisonSliceDiagram_right (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁)
    (h : c₁.vertex = c₀.vertex) :
    (SSet.uliftFunctor.{u + 1, u}).map s.right_inclusion ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram s =
      (SSet.uliftFunctor.{u + 1, u}).map s.right_index ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transportedCoconeSliceDiagram c₁ c₀.vertex h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (SSet.yonedaEquiv.symm c₀.vertex)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonSliceDiagram_uncurry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, transportedCoconeSliceDiagram_uncurry]
  exact s.right_augmentation

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
