module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonInitialState
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComparisonParityFaces

/-!
概要：元の初期実三角形から、偶数・奇数面の初期全比較データを構成する。
方針：標準辺と両標準点の恒等同型を使い、元の二端点面を計算する。
規約：初期幾何の存在を新しい仮定にしない。使われ方：元の二表示からの全部分列比較。

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


/-- 全比較の初期標準辺と両前置点を、元の全包含とともに保持する。 -/
structure ComparisonParityData {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    {I₀ I₁ : SSet.{u}} {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    {c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀} {c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactPresentationComparison μ D₀ D₁ c₀ c₁) where
  whole : s.shape ≅ (Δ[1] : SSet.{u})
  left : s.left_shape ≅ (Δ[0] : SSet.{u})
  right : s.right_shape ≅ (Δ[0] : SSet.{u})
  left_face : s.left_inclusion ≫ whole.hom = left.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace 0
  right_face : s.right_inclusion ≫ whole.hom = right.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace 0

private lemma comparisonEvenFace_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace.{u} 0 = SSet.stdSimplex.δ (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  rfl

private lemma comparisonOddFace_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace.{u} 0 = SSet.stdSimplex.δ (0 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- 元の二脚を結ぶ初期実三角形は、初期の全偶数・奇数面データを与える。 -/
def comparisonInitialParityData {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
    (c₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₀) (c₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D₁)
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₀.app _ (ULift.up a)))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D₁.app _ (ULift.up b)))
    (e : C.Edge (D₀.app _ (ULift.up a)) (D₁.app _ (ULift.up b)))
    (T : e.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c₁ (ULift.up b))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c₀ (ULift.up a)).ofEq rfl hv)) :
    ComparisonParityData (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonInitialState c₀ c₁ hv a b ha hb e T) where
  whole := Iso.refl _
  left := Iso.refl _
  right := Iso.refl _
  left_face := by
    change SSet.stdSimplex.δ (1 : Fin 2) ≫ 𝟙 _ = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonEvenFace 0
    rw [Category.comp_id, Category.id_comp]
    exact comparisonEvenFace_zero.symm
  right_face := by
    change SSet.stdSimplex.δ (0 : Fin 2) ≫ 𝟙 _ = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.comparisonOddFace 0
    rw [Category.comp_id, Category.id_comp]
    exact comparisonOddFace_zero.symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
