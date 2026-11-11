module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomClosedComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedChainMapQuasiIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Reflection
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 同じ DK 豊穣後合成の実単体は、元の閉零元の定数との AW 合成。 -/
lemma dgStandardSimplicialPostcomp_app (x y z : D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y) _⦋n⦌) :
    (eHomWhiskerLeft SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) f).app (Opposite.op ⦋n⦌) s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D y z f) n) s := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) y z).map
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z) f)) s = _
  congr 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (OrderHom.const _ (0 : Fin 1))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) y z).symm (closedHomEquiv R D y z f)) = _
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant
  congr 1
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := R) (D := D) y z).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D y z f).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent (n := 0) Finset.univ 0 Finset.univ_nonempty (by simp)
      (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D y z f).val).component Finset.univ 0 Finset.univ_nonempty (by simp)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.singleComponent_self (n := 0) _ _ _ _ (closedHomEquiv R D y z f).val).symm
/-- 同じ DK 後合成と同じ実 pinched 後合成は、標準同型を介して厳密に可換。 -/
lemma dgStandardSimplicialPostcomp_pinched (x y z : D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z) :
    (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) f) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x z).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition R D (x := x) f := by
  ext n s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x z).hom.app _
    (ULift.up ((eHomWhiskerLeft SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) f).app _ s.down)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition R D (x := x) f).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).hom.app _ s)
  rw [dgStandardSimplicialPostcomp_app]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomComposition_closed_post R D f
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).hom.app (Opposite.op n.unop) s)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_app, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex] at h
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedIso_inv_hom_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) y z).symm,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedIso_inv_hom_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).symm] at h
  exact h
lemma dgStandardSimplicialPostcomp_isQCatEquivalence
    (x y z : D)
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    [QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) f)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (eHomWhiskerLeft SSet (ForgetEnrichment.of (Complex R) x) f) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpaceKan x y
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x z) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpaceKan x z
  have hp := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_quasiIso_equivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) f)).isQCatEquivalence
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y)).isQCatEquivalence
  have H := hi.comp hp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPostcomposition R D (x := x) f) at H
  rw [← dgStandardSimplicialPostcomp_pinched R D x y z f] at H
  have hU := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x z)).isQCatEquivalence.cancel_right H
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isQCatEquivalence_ulift_iff_of_kan.{u, v}
    (eHomWhiskerLeft SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) f)).mp hU
end SerrePositivity.InfinityCategories.Project.DerivedCategories
