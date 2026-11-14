module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGCoefficientSkeletalStage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPrecompositionMaps

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

/-- 一段更新した元係数の指定部分は、合成閉分母による元の部分係数である。 -/
lemma refined_source_boundary : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase i (n + 1) ≫ U.sourceMap =
    a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D (y := y) (U.denominator ≫ S.denominator) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.skeletonBase_succ i n, Category.assoc, U.previous, ← Category.assoc,
    S.boundary, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_map_comp]

/-- 二段の閉分母後の元の商図式は、合成閉分母後の同じ図式である。 -/
lemma refinement_before :
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map S.denominator)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map U.denominator) =
    g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)) := by
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPrecomposition_comp]

/-- 既存の全体比較を追加閉分母で前合成し、合成分母の始点へ揃える。 -/
def refinedComparisonLeft : SSet.Homotopy
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
        ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)))
    (S.quotientMap ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map U.denominator)) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp S.homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map U.denominator)))
    (DGCoefficientSkeletalStage.refinement_before A D P i n x y a g S U) rfl

/-- 始点を読み替えた比較の全時間の射は、元の射の同じ後合成である。 -/
lemma refinedComparisonLeft_h :
    (DGCoefficientSkeletalStage.refinedComparisonLeft A D P i n x y a g S U).h =
      S.homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj S.source)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map U.denominator) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyRetarget_h _ _ _

/-- 更新した既存比較も指定部分を全時刻固定する。 -/
lemma refinedComparisonLeft_fixed : (i ▷ (Δ[1] : SSet.{max u v})) ≫
    (DGCoefficientSkeletalStage.refinedComparisonLeft A D P i n x y a g S U).h =
      fst L Δ[1] ≫ i ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj U.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
          ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map (U.denominator ≫ S.denominator)) := by
  rw [DGCoefficientSkeletalStage.refinedComparisonLeft_h, ← Category.assoc, S.fixed]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientPrecomposition_comp]

end DGCoefficientSkeletalStage
end SerrePositivity.InfinityCategories.Project.DerivedCategories
