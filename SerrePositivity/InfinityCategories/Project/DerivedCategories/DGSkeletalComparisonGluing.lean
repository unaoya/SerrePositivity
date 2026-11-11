module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalComparisonPieces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SkeletalHomotopyGluing

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
namespace DGSkeletalCellRefinement
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement A D P i n x y f g)
variable (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
  (skeletonOfMono i n).ι ≫ g)

/-- 各セルの境界全時刻は下骨格の定値比較と一致する。 -/
lemma comparison_boundary (c : Cell i n) :
    ((∂Δ[n]).ι ▷ (Δ[1] : SSet.{max u v})) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c).h =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary i n c ▷ (Δ[1] : SSet.{max u v})) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.cellComparison_h,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.previousComparison_h]
  exact (C.comparison c).boundary.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellBoundary_constant i n c (g ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator)))

/-- 次骨格全体の元の商写像と新しい元係数の商像を比較する。 -/
def skeletalComparison : SSet.Homotopy C.quotientBefore C.quotientAfter :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalHomotopyGlue i n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf)
    (fun c => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c)
    (DGSkeletalCellRefinement.comparison_boundary A D P i n x y f g C hf)

/-- 次骨格の比較は下骨格で全時刻定値である。 -/
lemma skeletalComparison_previous : (r i n ▷ (Δ[1] : SSet.{max u v})) ≫
    (DGSkeletalCellRefinement.skeletalComparison A D P i n x y f g C hf).h =
      fst (skeletonOfMono i n : SSet) Δ[1] ≫ (skeletonOfMono i n).ι ≫ g ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
          (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
          (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalHomotopyGlue_previous i n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf)
    (fun c => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c)
    (DGSkeletalCellRefinement.comparison_boundary A D P i n x y f g C hf)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.previousComparison_h A D P i n x y f g C hf)

/-- 次骨格の比較は各新セルの選んだ比較の全時刻を保つ。 -/
lemma skeletalComparison_cell (c : Cell i n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ▷ (Δ[1] : SSet.{max u v})) ≫
      (DGSkeletalCellRefinement.skeletalComparison A D P i n x y f g C hf).h =
        (C.comparison c).homotopy.h :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalHomotopyGlue_cell i n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf)
    (fun c => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c)
    (DGSkeletalCellRefinement.comparison_boundary A D P i n x y f g C hf) c).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.cellComparison_h A D P i n x y f g C c)

end DGSkeletalCellRefinement
end SerrePositivity.InfinityCategories.Project.DerivedCategories
