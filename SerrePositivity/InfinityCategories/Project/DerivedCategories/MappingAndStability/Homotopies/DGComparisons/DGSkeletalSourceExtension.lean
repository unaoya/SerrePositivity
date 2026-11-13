module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSkeletalCellRefinement
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedPrecompositionMaps

/-! # 共通閉分母後の下骨格の実係数延長

概要：全新セルの充填を貼り、次骨格の元係数写像を構成して全ての制限を保持する。
方針：共通閉分母の前合成で下骨格を更新し、指定セル単体と pushout で貼る。
規約：商比較も下骨格で厳密に揃える。使われ方：一般有限対の相対骨格帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet SSet.relativeCellComplexOfMono
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
variable (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y))
namespace DGSkeletalCellRefinement
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement A D P i n x y f g)

/-- 共通閉分母後の全新セルを貼り合わせた、次骨格の元係数写像。 -/
def sourceExtension : (skeletonOfMono i (n + 1) : SSet) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D C.source y :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellGlue i n (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D C.denominator)
    (fun c => SSet.yonedaEquiv.symm (C.simplex c)) C.boundary

/-- 次骨格の係数写像は、下骨格の同じ閉前合成を厳密に保つ。 -/
lemma sourceExtension_previous : r i n ≫ C.sourceExtension =
    f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A D C.denominator :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellGlue_previous _ _ _ _ _

/-- 次骨格の各新セルは、選んだ同じ実充填単体である。 -/
lemma sourceExtension_cell (c : Cell i n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellInclusion i n c ≫ C.sourceExtension = SSet.yonedaEquiv.symm (C.simplex c) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.skeletalCellGlue_cell _ _ _ _ _ c

/-- 下骨格の商比較は元の全体商写像の同じ閉前合成と厳密に一致する。 -/
lemma sourceExtension_previous_comparison
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i n).ι ≫ g) :
    r i n ≫ C.sourceExtension ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map C.source y) =
      (skeletonOfMono i n).ι ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator) := by
  rw [← Category.assoc, C.sourceExtension_previous, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_map_naturality, ← Category.assoc, hf, Category.assoc]

end DGSkeletalCellRefinement
end SerrePositivity.InfinityCategories.Project.DerivedCategories
