module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceUnitComponents
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorHomSquareRealization

/-!
概要：差の単位の二成分と両端の元の矢印を固定した、実際の coherent な正方形。
方針：C 枝の零性と、可逆余単位で相殺した D 枝の零合成を h Fun で比較し実現する。
規約：写像空間の同値性は後続。使われ方：元の lax pullback 内の単位の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
local instance unitSquareFunctorZero (A X : SSet.{u}) [Quasicategory X] [HasZeroVertex X] :
    HasZeroVertex ((ihom A).obj X) := functorHasZeroVertex A X
local instance unitSquareFunctorZeroMorphisms (A X : SSet.{u})
    [Quasicategory X] [HasZeroVertex X] : HasZeroMorphisms ((ihom A).obj X).HomotopyCategory :=
  hasZeroMorphisms_ho

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  {v : E.obj ⟶ D.obj} (a : QCatAdjunction q.hom v) (hv : IsFullyFaithful v)

include hv in
lemma laxDifferenceUnitSquare_comm :
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (laxArrowHomotopy p q)) ≫
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
          (functorHomotopyPostcomp (laxDifferenceUnitDHomotopy p q v a) q.hom)) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (laxDifferenceUnitCHomotopy p q v) p.hom)) ≫
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (laxDifferenceUnitTargetArrowHomotopy p q v)) := by
  have hr : Arrow.mk
      ((hoFunctor.map ((ihom (laxCategory p q).obj).map q.hom)).toFunctor.map
        (laxDifferenceUnitD p q a)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp (laxDifferenceUnitDHomotopy p q v a) q.hom))) := by
    have h := functorHomotopyPostcomp_hom (functorHomHomotopy (laxDifferenceUnitD p q a)) q.hom
    rw [functorHomHomotopy_hom] at h
    exact (congrArg Arrow.mk h).symm.trans
      (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ rfl)
  have hz := comp_zero_of_arrowMk_eq (laxArrowHom p q) _
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (laxArrowHomotopy p q))) _ rfl hr (laxDifferenceUnitD_nullComposite p q a hv)
  have ht : IsZeroVertex (functorVertex
      (((laxDifference p q ≫ laxDifferenceRho p q v) ≫ (laxFst p q).hom) ≫ p.hom)) :=
    ⟨isInitialVertex_functorVertex_of_pointwise _
      (fun x => (laxDifferenceUnit_target_fst_post_zero p q v x).1),
      isTerminalVertex_functorVertex_of_pointwise _
        (fun x => (laxDifferenceUnit_target_fst_post_zero p q v x).2)⟩
  have hl := ht.isZeroHo.eq_zero_of_tgt
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (laxDifferenceUnitCHomotopy p q v) p.hom)))
  rw [hz, hl, zero_comp]

/-- 四つの元の代表ホモトピーを境界として保持する関手正方形。 -/
def laxDifferenceUnitSquare : SerrePositivity.InfinityCategories.FunctorHomSquare (laxArrowHomotopy p q)
    (laxDifferenceUnitTargetArrowHomotopy p q v)
    (functorHomotopyPostcomp (laxDifferenceUnitCHomotopy p q v) p.hom)
    (functorHomotopyPostcomp (laxDifferenceUnitDHomotopy p q v a) q.hom) :=
  Classical.choice (HomotopyLimits.nonempty_functorHomSquare_of_homEq _ _ _ _
    (laxDifferenceUnitSquare_comm p q a hv))

end SerrePositivity.KST.LocalizingInvariants
