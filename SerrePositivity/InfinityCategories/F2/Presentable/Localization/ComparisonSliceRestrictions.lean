module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.ComparisonSequenceSliceDiagram
public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceDiagram

/-!
概要：元の両表示余錐を同じ大域頂点の slice 内で比較する。
方針：公開 P の余錐 slice 表示を等しい頂点間で移し、全 uncurry の単射性を使う。
規約：両側の元の全余錐を保持する。使われ方：共通全比較の部分列との厳密な一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 指定余錐の slice 表示を、等しい指定大域頂点の slice へ移す。 -/
def transportedCoconeSliceDiagram {K C : SSet.{u}} {D : K ⟶ C}
    (c : JoinCocone D) (z : C _⦋0⦌) (h : c.vertex = z) :
    K ⟶ sliceOver (SSet.yonedaEquiv.symm z) :=
  coconeSliceDiagram c ≫
    (eqToIso (congrArg (fun y ↦ sliceOver (SSet.yonedaEquiv.symm y)) h)).hom

/-- 大域頂点の等号による移送は元の全余錐値を保持する。 -/
lemma transportedCoconeSliceDiagram_uncurry {K C : SSet.{u}} {D : K ⟶ C}
    (c : JoinCocone D) (z : C _⦋0⦌) (h : c.vertex = z) :
    sliceOverUncurry (transportedCoconeSliceDiagram c z h) = c.val := by
  cases h
  dsimp only [transportedCoconeSliceDiagram]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact coconeSliceDiagram_uncurry c

/-- 同じ移送の後でも、元の全底図式が射影で回収される。 -/
lemma transportedCoconeSliceDiagram_projection {K C : SSet.{u}} {D : K ⟶ C}
    (c : JoinCocone D) (z : C _⦋0⦌) (h : c.vertex = z) :
    transportedCoconeSliceDiagram c z h ≫ sliceOverProjection (SSet.yonedaEquiv.symm z) = D := by
  cases h
  dsimp only [transportedCoconeSliceDiagram]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact coconeSliceDiagram_projection c

variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}

/-- 左側の元の全余錐は、同じ大域頂点上の全比較図式に厳密に含まれる。 -/
lemma comparisonSliceDiagram_left (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁) :
    (SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion ≫ comparisonSliceDiagram s =
      (SSet.uliftFunctor.{u + 1, u}).map s.left_index ≫ coconeSliceDiagram c₀ := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm c₀.vertex)
  rw [sliceOverUncurry_precomp, comparisonSliceDiagram_uncurry,
    sliceOverUncurry_precomp, coconeSliceDiagram_uncurry]
  exact s.left_augmentation

/-- 右側についても、元の同じ大域頂点上へ移した全余錐を厳密に回収する。 -/
lemma comparisonSliceDiagram_right (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁)
    (h : c₁.vertex = c₀.vertex) :
    (SSet.uliftFunctor.{u + 1, u}).map s.right_inclusion ≫ comparisonSliceDiagram s =
      (SSet.uliftFunctor.{u + 1, u}).map s.right_index ≫
        transportedCoconeSliceDiagram c₁ c₀.vertex h := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm c₀.vertex)
  rw [sliceOverUncurry_precomp, comparisonSliceDiagram_uncurry,
    sliceOverUncurry_precomp, transportedCoconeSliceDiagram_uncurry]
  exact s.right_augmentation

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
