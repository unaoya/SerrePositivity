module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientStageRefinementMaps

/-! # 骨格段の全体比較の境界固定合成

概要：追加分母後の既存比較と新しい一段比較を、元の部分図式を固定して合成する。
方針：下骨格固定を指定部分へ制限し、既存比較の終点等式と合成前合成で揃える。
規約：比較は指定部分の全時刻を固定する。使われ方：相対骨格状態の後続段。
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
variable (a : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
namespace DGCoefficientSkeletalStage
variable (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientSkeletalStage A D P i n x y a g)
variable (U : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientSkeletalStep A D P i n S.source y S.sourceMap S.quotientMap)

/-- 状態の全体商写像も指定部分上で元の商前合成に厳密に一致する。 -/
lemma quotientMap_boundary : i ≫ S.quotientMap =
    i ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map S.denominator) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fixedDiagramHomotopy_target i _ S.homotopy S.fixed

/-- 一段の比較も元の指定部分を合成分母上で全時刻固定する。 -/
lemma refinedComparisonRight_fixed : (i ▷ (Δ[1] : SSet.{max u v})) ≫ U.homotopy.h =
    fst L Δ[1] ≫ i ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fixedDiagramHomotopy_restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i n) (skeletonOfMono i n).ι
    ((skeletonOfMono i n).ι ≫ S.quotientMap ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map U.denominator))
    U.homotopy U.fixed
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i n ≫ (skeletonOfMono i n).ι = i := rfl
  rw [hb, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i n), hb] at h
  rw [h, ← Category.assoc i S.quotientMap,
    DGCoefficientSkeletalStage.quotientMap_boundary A D P i n x y a g S]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPrecomposition_comp]

/-- 二つの比較を、元の指定部分で定値な一つの全体比較に合成できる。 -/
theorem refinedComparison_nonempty [Mono i] :
    ∃ H : SSet.Homotopy
      (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
          ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map (U.denominator ≫ S.denominator))) U.quotientMap,
      (i ▷ (Δ[1] : SSet.{max u v})) ≫ H.h =
        fst L Δ[1] ≫ i ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
          (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
          (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
            ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fixedDiagramHomotopyComposite_exists i _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientSkeletalStage.refinedComparisonLeft A D P i n x y a g S U)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoefficientSkeletalStage.refinedComparisonLeft_fixed A D P i n x y a g S U)
    U.homotopy (DGCoefficientSkeletalStage.refinedComparisonRight_fixed A D P i n x y a g S U)

end DGCoefficientSkeletalStage
end SerrePositivity.InfinityCategories.Project.DerivedCategories
