module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGSkeletalComparisonGluing
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.KanHomotopyExtension

/-! # 次骨格の商比較の全体への延長

概要：次骨格に貼った商比較を全体へ延長し、次骨格上で厳密な比較正方形を作る。
方針：商の pinched Hom の Kan 性で指定比較の全時刻を延長する。
規約：下骨格の比較は全時刻定値に保つ。使われ方：一般有限対の係数充填の帰納。
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

/-- 一段更新後の全体商写像と指定次骨格比較の厳密延長。 -/
structure DGSkeletalQuotientExtension (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement A D P i n x y f g)
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
      (skeletonOfMono i n).ι ≫ g) where
  map : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P) ((inclusion A D P).obj C.source)
    ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)
  square : (skeletonOfMono i (n + 1)).ι ≫ map = C.quotientAfter
  homotopy : SSet.Homotopy
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator)) map
  restriction : ((skeletonOfMono i (n + 1)).ι ▷ (Δ[1] : SSet.{max u v})) ≫ homotopy.h =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.skeletalComparison A D P i n x y f g C hf).h

/-- 次骨格の全時刻比較を保つ全体商写像の更新が存在する。 -/
theorem dgSkeletalQuotientExtension_nonempty
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement A D P i n x y f g)
    (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
      (skeletonOfMono i n).ι ≫ g) :
    Nonempty (DGSkeletalQuotientExtension A D P i n x y f g C hf) := by
  obtain ⟨g', H, hg', hH⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanHomotopyExtension_exists (skeletonOfMono i (n + 1)).ι
    (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
      (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator))
    C.quotientAfter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.skeletalComparison A D P i n x y f g C hf)
  exact ⟨⟨g', hg', H, hH⟩⟩

namespace DGSkeletalQuotientExtension
variable {C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement A D P i n x y f g}
variable {hf : f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map x y) =
  (skeletonOfMono i n).ι ≫ g}
variable (E : DGSkeletalQuotientExtension A D P i n x y f g C hf)

/-- 全体の比較も下骨格上の全時刻を定値に保つ。 -/
lemma homotopy_previous : ((skeletonOfMono i n).ι ▷ (Δ[1] : SSet.{max u v})) ≫
    E.homotopy.h = fst (skeletonOfMono i n : SSet) Δ[1] ≫ (skeletonOfMono i n).ι ≫ g ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj C.source) (x := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x)
        (y := (_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).onClosed.map C.denominator) := by
  have hi : r i n ≫ (skeletonOfMono i (n + 1)).ι = (skeletonOfMono i n).ι := rfl
  rw [← hi, comp_whiskerRight, Category.assoc, E.restriction]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSkeletalCellRefinement.skeletalComparison_previous A D P i n x y f g C hf

end DGSkeletalQuotientExtension
end SerrePositivity.InfinityCategories.Project.DerivedCategories
