module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedPrecompositionAW

/-! 実閉射との AW 後合成は、標的の小ささを仮定せず、同じ全 Hom 鎖後合成に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

lemma dgGluingPinchedCompositionFamily_closed_post {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    (f : K ⟶ DGNerve.pinchedHom R D x y) :
    pinchedHomCompositionFamily f (SSet.const (pinchedClosedVertex R D s)) =
      f ≫ pinchedHomChainMap (D := D) (E := D)
        (x := x) (y := y) (x' := x) (y' := z)
        (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) s) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (pinchedHomComposition x y z).app _
      (f.app _ k, (SSet.const (X := K) (pinchedClosedVertex R D s)).app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, pinchedHomComposition_closed_post]
  rfl

end SerrePositivity.InfinityCategories
