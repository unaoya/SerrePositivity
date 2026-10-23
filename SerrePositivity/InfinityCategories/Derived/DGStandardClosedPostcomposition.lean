module
public import SerrePositivity.InfinityCategories.Derived.PinchedHomClosedComposition
public import SerrePositivity.InfinityCategories.DoldKanComparison.SimplicialCategory
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapQuasiIso
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection
/-!
概要：DK の豊穣後合成を、同じ dg 閉零射による実 pinched 後合成に厳密に照合する。
方針：同じ閉零元の AW 定数作用と実 pinched 同型の合成計算を使う。
規約：全次数・全単体の実等式。使われ方：準同型から実 coslice 輸送の同値性への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DoldKanComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 同じ DK 豊穣後合成の実単体は、元の閉零元の定数との AW 合成。 -/
lemma dgStandardSimplicialPostcomp_app (x y z : D)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    (n : ℕ) (s : (standardHomSpace (R := R) (D := D) x y) _⦋n⦌) :
    (eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f).app (Opposite.op ⦋n⦌) s =
      standardAW (standardConstant (closedHomEquiv R D y z f) n) s := by
  change standardAW ((standardHomSpace (R := R) (D := D) y z).map
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (closedStandardVertexEquiv (R := R) (D := D)
      (ForgetEnrichment.of (Complex R) y) (ForgetEnrichment.of (Complex R) z) f)) s = _
  congr 1
  change standardPullback (OrderHom.const _ (0 : Fin 1))
    ((standardZeroEquiv (R := R) (D := D) y z).symm (closedHomEquiv R D y z f)) = _
  unfold standardConstant
  congr 1
  apply (standardZeroEquiv (R := R) (D := D) y z).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (closedHomEquiv R D y z f).val =
    (singleComponent (n := 0) Finset.univ 0 Finset.univ_nonempty (by simp)
      (closedHomEquiv R D y z f).val).component Finset.univ 0 Finset.univ_nonempty (by simp)
  exact (singleComponent_self (n := 0) _ _ _ _ (closedHomEquiv R D y z f).val).symm
/-- 同じ DK 後合成と同じ実 pinched 後合成は、標準同型を介して厳密に可換。 -/
lemma dgStandardSimplicialPostcomp_pinched (x y z : D)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z) :
    (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f) ≫
      (standardHomPinchedIso (R := R) (D := D) x z).hom =
    (standardHomPinchedIso (R := R) (D := D) x y).hom ≫
      pinchedClosedPostcomposition R D (x := x) f := by
  ext n s
  change (standardHomPinchedIso (R := R) (D := D) x z).hom.app _
    (ULift.up ((eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f).app _ s.down)) =
    (pinchedClosedPostcomposition R D (x := x) f).app _
      ((standardHomPinchedIso (R := R) (D := D) x y).hom.app _ s)
  rw [dgStandardSimplicialPostcomp_app]
  have h := pinchedHomComposition_closed_post R D f
    ((standardHomPinchedIso (R := R) (D := D) x y).hom.app (Opposite.op n.unop) s)
  rw [pinchedHomComposition_app, pinchedClosedStandardSimplex] at h
  erw [pinchedIso_inv_hom_apply (standardHomPinchedIso (R := R) (D := D) y z).symm,
    pinchedIso_inv_hom_apply (standardHomPinchedIso (R := R) (D := D) x y).symm] at h
  exact h
lemma dgStandardSimplicialPostcomp_isQCatEquivalence
    (x y z : D)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    [QuasiIso (dgClosedPostcomposition R D (x := x) f)] :
    IsQCatEquivalence (eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f) := by
  let : KanComplex (standardHomSpace (R := R) (D := D) x y) := standardHomSpaceKan x y
  let : KanComplex (standardHomSpace (R := R) (D := D) x z) := standardHomSpaceKan x z
  have hp := (pinchedHomChainMap_quasiIso_equivalence
    (dgClosedPostcomposition R D (x := x) f)).isQCatEquivalence
  have hi := (qCatEquivalenceOfIso (standardHomPinchedIso (R := R) (D := D) x y)).isQCatEquivalence
  have H := hi.comp hp
  change IsQCatEquivalence ((standardHomPinchedIso (R := R) (D := D) x y).hom ≫
    pinchedClosedPostcomposition R D (x := x) f) at H
  rw [← dgStandardSimplicialPostcomp_pinched R D x y z f] at H
  have hU := (qCatEquivalenceOfIso
    (standardHomPinchedIso (R := R) (D := D) x z)).isQCatEquivalence.cancel_right H
  exact (isQCatEquivalence_ulift_iff_of_kan.{u, v}
    (eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f)).mp hU
end SerrePositivity.InfinityCategories
