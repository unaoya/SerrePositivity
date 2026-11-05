module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceRhoArrowMapping
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroSourceMapping

/-!
概要：lax 矢印関手と cofiber の合成は、ρ(y) への元の写像空間を保つ。
方針：ρ(y) の矢印の始点は零なので、二つの実比較の同値を合成する。
規約：選ばれた cofiber 関手の合成。使われ方：元の差の関手の局所比較。
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
variable {C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (v : E.obj ⟶ D.obj)

lemma laxDifferenceRho_arrow_zeroSource (y : E.obj _⦋0⦌) :
    IsZeroSourceArrow ((F2.laxPullbackArrow p.hom q.hom).app (Opposite.op ⦋0⦌)
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) := by
  change IsZeroVertex ((F2.laxPullbackArrow p.hom q.hom ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) _)
  rw [F2.laxPullbackArrow_source]
  change IsZeroVertex (p.hom.app (Opposite.op ⦋0⦌)
    ((F2.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌) _))
  rw [laxDifferenceRho_fst_vertex]
  exact IsExactFunctor.preservesZero (F := p.hom) _ (chosenZeroVertex C.obj).isZero

lemma laxDifferenceCompositeMapping_equivalence (a : QCatAdjunction q.hom v)
    (hv : IsFullyFaithful v) (x : (laxCategory p q).obj _⦋0⦌) (y : E.obj _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap
      (F2.laxPullbackArrow p.hom q.hom ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber E.obj
        (𝟙 ((ihom (Δ[1] : SSet.{u})).obj E.obj))) x
      ((laxDifferenceRho p q v).app (Opposite.op ⦋0⦌) y)) := by
  rw [pinchedHomMap_comp]
  exact ((laxDifferenceRho_arrowMapping_equivalence p q v a hv x y).isQCatEquivalence.comp
    (cofiberZeroSourceMapping_equivalence E.obj _ _
      (laxDifferenceRho_arrow_zeroSource p q v y)).isQCatEquivalence
    ).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
