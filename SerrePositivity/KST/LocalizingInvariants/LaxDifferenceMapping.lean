module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceCompositeMapping
public import SerrePositivity.KST.LocalizingInvariants.MappingFunctorIso

/-!
概要：元の差の関手は、ρ(y) への元の写像空間に同値を誘導する。
方針：lax 矢印と cofiber の合成の比較を、全族 cofiber の実関手同型で戻す。
規約：laxDifference 自体の pinchedHomMap。使われ方：Tamme Prop. 11 の随伴構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (v : E.obj ⟶ D.obj)

lemma laxDifferenceMapping_equivalence (a : QCatAdjunction q.hom v)
    (hv : IsFullyFaithful v) (x : (laxCategory p q).obj _⦋0⦌) (y : E.obj _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap (laxDifference p q) x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) :=
  pinchedHomMap_equivalence_of_functorIso
    (CofiberFamily.compositionIso E.obj (F2.laxPullbackArrow p.hom q.hom)) x _
    (laxDifferenceCompositeMapping_equivalence p q v a hv x y)

end SerrePositivity.KST.LocalizingInvariants
