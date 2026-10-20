module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientSkeletalStage
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPrecompositionMaps

/-! # 骨格段の追加閉分母による更新の等式

概要：追加分母で元係数の部分制限と商比較の始点を更新する。
方針：元と商の全単体前合成の合成則で、二段の前合成を合成閉分母へ揃える。
規約：比較の全時間の射をそのまま後合成する。使われ方：骨格状態の後続段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (a : L ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))
namespace DGCoefficientSkeletalStage
variable (S : DGCoefficientSkeletalStage A D P i n x y a g)
variable (U : DGCoefficientSkeletalStep A D P i n S.source y S.sourceMap S.quotientMap)

/-- 一段更新した元係数の指定部分は、合成閉分母による元の部分係数である。 -/
lemma refined_source_boundary : skeletonBase i (n + 1) ≫ U.sourceMap =
    a ≫ pinchedClosedPrecomposition A D (y := y) (U.denominator ≫ S.denominator) := by
  rw [← skeletonBase_succ i n, Category.assoc, U.previous, ← Category.assoc,
    S.boundary, Category.assoc, pinchedClosedPrecomposition_map_comp]

/-- 二段の閉分母後の元の商図式は、合成閉分母後の同じ図式である。 -/
lemma refinement_before :
    (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj S.source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map S.denominator)) ≫
      pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj S.source)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map U.denominator) =
    g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y)
        ((inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)) := by
  rw [Category.assoc, dgQuotientPrecomposition_comp]

/-- 既存の全体比較を追加閉分母で前合成し、合成分母の始点へ揃える。 -/
def refinedComparisonLeft : SSet.Homotopy
    (g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y)
        ((inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)))
    (S.quotientMap ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj S.source)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map U.denominator)) :=
  stableHomotopyRetarget (functorHomotopyPostcomp S.homotopy
    (pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj S.source)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map U.denominator)))
    (DGCoefficientSkeletalStage.refinement_before A D P i n x y a g S U) rfl

/-- 始点を読み替えた比較の全時間の射は、元の射の同じ後合成である。 -/
lemma refinedComparisonLeft_h :
    (DGCoefficientSkeletalStage.refinedComparisonLeft A D P i n x y a g S U).h =
      S.homotopy.h ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj S.source)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map U.denominator) :=
  homotopyRetarget_h _ _ _

/-- 更新した既存比較も指定部分を全時刻固定する。 -/
lemma refinedComparisonLeft_fixed : (i ▷ (Δ[1] : SSet.{max u v})) ≫
    (DGCoefficientSkeletalStage.refinedComparisonLeft A D P i n x y a g S U).h =
      fst L Δ[1] ≫ i ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj U.source) (x := (inclusion A D P).obj x)
        (y := (inclusion A D P).obj y)
          ((inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)) := by
  rw [DGCoefficientSkeletalStage.refinedComparisonLeft_h, ← Category.assoc, S.fixed]
  simp only [Category.assoc]
  rw [dgQuotientPrecomposition_comp]

end DGCoefficientSkeletalStage
end SerrePositivity.InfinityCategories
