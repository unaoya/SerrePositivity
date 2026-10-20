module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientStageComparison

/-! # 係数骨格状態の後続段の存在

概要：有限な全新セルの同時充填と全体比較の合成から、次の骨格状態を作る。
方針：追加閉分母を合成し、厳密な制限・商正方形・境界固定比較を一括して引き継ぐ。
規約：元の部分係数と商図式を変更しない。使われ方：一般有限対の係数充填の帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) [Mono i] [K.Finite]
variable (n : ℕ) (x y : D) (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))

/-- 既存の骨格状態は一つの追加閉分母後に次の状態を持つ。 -/
theorem dgCoefficientSkeletalSuccessor_nonempty (hP : localKFlat A D P)
    (S : DGCoefficientSkeletalStage A D P i n x y a g) :
    Nonempty (DGCoefficientSkeletalStage A D P i (n + 1) x y a g) := by
  obtain ⟨U⟩ := dgCoefficientSkeletalStep_nonempty A D P i n S.source y
    S.sourceMap S.quotientMap hP S.square
  obtain ⟨H, hH⟩ := DGCoefficientSkeletalStage.refinedComparison_nonempty
    A D P i n x y a g S U
  exact ⟨{
    source := U.source
    denominator := U.denominator ≫ S.denominator
    denominator_mem := dgClosedVerdierDenominator_comp A D P U.denominator S.denominator
      U.denominator_mem S.denominator_mem
    sourceMap := U.sourceMap
    quotientMap := U.quotientMap
    boundary := DGCoefficientSkeletalStage.refined_source_boundary A D P i n x y a g S U
    square := U.square
    homotopy := H
    fixed := hH }⟩

end SerrePositivity.InfinityCategories
