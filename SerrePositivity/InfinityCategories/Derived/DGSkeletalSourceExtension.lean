module
public import SerrePositivity.InfinityCategories.Derived.DGSkeletalCellRefinement
public import SerrePositivity.InfinityCategories.Derived.PinchedPrecompositionMaps

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {L K : SSet.{max u v}} (i : L ⟶ K) (n : ℕ) (x y : D)
variable (f : (skeletonOfMono i n : SSet) ⟶ DGNerve.pinchedHom A D x y)
variable (g : K ⟶ DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj x) ((inclusion A D P).obj y))
namespace DGSkeletalCellRefinement
variable (C : DGSkeletalCellRefinement A D P i n x y f g)

/-- 共通閉分母後の全新セルを貼り合わせた、次骨格の元係数写像。 -/
def sourceExtension : (skeletonOfMono i (n + 1) : SSet) ⟶
    DGNerve.pinchedHom A D C.source y :=
  skeletalCellGlue i n (f ≫ pinchedClosedPrecomposition A D C.denominator)
    (fun c => SSet.yonedaEquiv.symm (C.simplex c)) C.boundary

/-- 次骨格の係数写像は、下骨格の同じ閉前合成を厳密に保つ。 -/
lemma sourceExtension_previous : r i n ≫ C.sourceExtension =
    f ≫ pinchedClosedPrecomposition A D C.denominator :=
  skeletalCellGlue_previous _ _ _ _ _

/-- 次骨格の各新セルは、選んだ同じ実充填単体である。 -/
lemma sourceExtension_cell (c : Cell i n) :
    skeletalCellInclusion i n c ≫ C.sourceExtension = SSet.yonedaEquiv.symm (C.simplex c) :=
  skeletalCellGlue_cell _ _ _ _ _ c

/-- 下骨格の商比較は元の全体商写像の同じ閉前合成と厳密に一致する。 -/
lemma sourceExtension_previous_comparison
    (hf : f ≫ pinchedHomChainMap ((inclusion A D P).map x y) = (skeletonOfMono i n).ι ≫ g) :
    r i n ≫ C.sourceExtension ≫ pinchedHomChainMap ((inclusion A D P).map C.source y) =
      (skeletonOfMono i n).ι ≫ g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj C.source) (x := (inclusion A D P).obj x)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map C.denominator) := by
  rw [← Category.assoc, C.sourceExtension_previous, Category.assoc,
    pinchedClosedPrecomposition_map_naturality, ← Category.assoc, hf, Category.assoc]

end DGSkeletalCellRefinement
end SerrePositivity.InfinityCategories
