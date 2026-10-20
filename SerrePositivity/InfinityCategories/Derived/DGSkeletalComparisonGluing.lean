module
public import SerrePositivity.InfinityCategories.Derived.DGSkeletalComparisonPieces
public import SerrePositivity.InfinityCategories.Derived.SkeletalHomotopyGluing

/-! # 次骨格全体の商比較

概要：新セルの境界固定比較を下骨格の定値比較と貼り、次骨格全体で比較する。
方針：境界の全時刻を射影の自然性で照合し、骨格 pushout のホモトピー接着を使う。
規約：下骨格では全時刻で定値。使われ方：有限相対骨格の一段更新。
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
variable (f : (skeletonOfMono i n : SSet) ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))
namespace DGSkeletalCellRefinement
variable (C : DGSkeletalCellRefinement A D P i n x y f g)
variable (hf : f ≫ pinchedHomChainMap ((inclusion A D P).map x y) =
  (skeletonOfMono i n).ι ≫ g)

/-- 各セルの境界全時刻は下骨格の定値比較と一致する。 -/
lemma comparison_boundary (c : Cell i n) :
    ((∂Δ[n]).ι ▷ (Δ[1] : SSet.{max u v})) ≫
        (DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c).h =
      (skeletalCellBoundary i n c ▷ (Δ[1] : SSet.{max u v})) ≫
        (DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf).h := by
  rw [DGSkeletalCellRefinement.cellComparison_h,
    DGSkeletalCellRefinement.previousComparison_h]
  exact (C.comparison c).boundary.trans
    (skeletalCellBoundary_constant i n c (g ≫
      pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj C.source) (x := (inclusion A D P).obj x)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map C.denominator)))

/-- 次骨格全体の元の商写像と新しい元係数の商像を比較する。 -/
def skeletalComparison : SSet.Homotopy C.quotientBefore C.quotientAfter :=
  skeletalHomotopyGlue i n
    (DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf)
    (fun c => DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c)
    (DGSkeletalCellRefinement.comparison_boundary A D P i n x y f g C hf)

/-- 次骨格の比較は下骨格で全時刻定値である。 -/
lemma skeletalComparison_previous : (r i n ▷ (Δ[1] : SSet.{max u v})) ≫
    (DGSkeletalCellRefinement.skeletalComparison A D P i n x y f g C hf).h =
      fst (skeletonOfMono i n : SSet) Δ[1] ≫ (skeletonOfMono i n).ι ≫ g ≫
        pinchedClosedPrecomposition A (QuotientObject D P)
          (q := (inclusion A D P).obj C.source) (x := (inclusion A D P).obj x)
          (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map C.denominator) :=
  (skeletalHomotopyGlue_previous i n
    (DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf)
    (fun c => DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c)
    (DGSkeletalCellRefinement.comparison_boundary A D P i n x y f g C hf)).trans
      (DGSkeletalCellRefinement.previousComparison_h A D P i n x y f g C hf)

/-- 次骨格の比較は各新セルの選んだ比較の全時刻を保つ。 -/
lemma skeletalComparison_cell (c : Cell i n) :
    (skeletalCellInclusion i n c ▷ (Δ[1] : SSet.{max u v})) ≫
      (DGSkeletalCellRefinement.skeletalComparison A D P i n x y f g C hf).h =
        (C.comparison c).homotopy.h :=
  (skeletalHomotopyGlue_cell i n
    (DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf)
    (fun c => DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c)
    (DGSkeletalCellRefinement.comparison_boundary A D P i n x y f g C hf) c).trans
      (DGSkeletalCellRefinement.cellComparison_h A D P i n x y f g C c)

end DGSkeletalCellRefinement
end SerrePositivity.InfinityCategories
