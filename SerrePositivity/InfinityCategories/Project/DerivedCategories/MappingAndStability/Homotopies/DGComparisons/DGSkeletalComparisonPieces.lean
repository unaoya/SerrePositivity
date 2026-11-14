module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSkeletalSourceExtension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 骨格一段更新の商比較の各部分

概要：下骨格の定値比較と各セルの境界固定比較を、同じ二つの次骨格写像の制限へ揃える。
方針：厳密な前合成自然性とセル制限公式で二端点を照合する。
規約：比較の全時間の射は元のまま保つ。使われ方：次骨格全体の比較の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open CartesianMonoidalCategory SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
/-- 端点の等式でホモトピーを読み替えても全時刻の射は変わらない。 -/
lemma homotopyRetarget_h {L X : SSet.{w}} {a b a' b' : L ⟶ X}
    (H : SSet.Homotopy a b) (ha : a = a') (hb : b = b') :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget H ha hb).h = H.h := rfl

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
namespace DGSkeletalCellRefinement
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement A D P i n x y f g)

/-- 元の全体商写像の同じ閉前合成を次骨格へ制限する。 -/
def quotientBefore : (skeletonOfMono i (n + 1) : SSet) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P) ((inclusion A D P).obj C.source)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) :=
  (skeletonOfMono i (n + 1)).ι ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
    (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
    (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator)

/-- 新しい元係数写像を商へ送った次骨格写像。 -/
def quotientAfter : (skeletonOfMono i (n + 1) : SSet) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P) ((inclusion A D P).obj C.source)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) :=
  C.sourceExtension ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map C.source y)

/-- 商の元写像の各セルへの制限。 -/
lemma quotientBefore_cell (c : Cell i n) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ C.quotientBefore =
    c.map ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion quotientBefore
  rw [Category.assoc, Cell.ι_b_ι_assoc]

/-- 新しい商像の各セルへの制限。 -/
lemma quotientAfter_cell (c : Cell i n) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ C.quotientAfter =
    SSet.yonedaEquiv.symm (C.simplex c) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map C.source y) := by
  change _ ≫ (C.sourceExtension ≫ _) = _
  rw [← Category.assoc, C.sourceExtension_cell]

/-- 下骨格上の比較は定値な全時間の射で選べる。 -/
def previousComparison
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i n).ι ≫ g) :
    SSet.Homotopy (r i n ≫ C.quotientBefore) (r i n ≫ C.quotientAfter) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl
    ((skeletonOfMono i n).ι ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator))) rfl
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.sourceExtension_previous_comparison A D P i n x y f g C hf).symm

/-- 各セルの既存の比較を、同じ次骨格上の二写像の制限として読む。 -/
def cellComparison (c : Cell i n) : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ C.quotientBefore)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ C.quotientAfter) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (C.comparison c).homotopy
    (DGSkeletalCellRefinement.quotientBefore_cell A D P i n x y f g C c).symm
    (DGSkeletalCellRefinement.quotientAfter_cell A D P i n x y f g C c).symm

/-- 下骨格比較の全時刻の射は元の定値ホモトピーの射そのもの。 -/
lemma previousComparison_h
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
      (skeletonOfMono i n).ι ≫ g) :
    (DGSkeletalCellRefinement.previousComparison A D P i n x y f g C hf).h =
      fst (skeletonOfMono i n : SSet) Δ[1] ≫ (skeletonOfMono i n).ι ≫ g ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
          (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
          (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator) := rfl

/-- セル比較の全時刻の射は選んだ係数比較の射そのもの。 -/
lemma cellComparison_h (c : Cell i n) :
    (DGSkeletalCellRefinement.cellComparison A D P i n x y f g C c).h =
      (C.comparison c).homotopy.h :=
  homotopyRetarget_h (C.comparison c).homotopy _ _

end DGSkeletalCellRefinement
end SerrePositivity.InfinityCategories.Project.DerivedCategories
