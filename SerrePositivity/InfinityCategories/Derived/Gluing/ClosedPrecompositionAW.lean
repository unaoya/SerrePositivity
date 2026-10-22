module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedPrecompositionComponents
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedStandardConstant

/-! 閉 augmentation との AW 前合成は、対象圏の小ささなしに元の豊穣前合成と一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

lemma dgGluingPinchedComposition_closed_pre {x y z : D}
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    {n : ℕ} (g : (DGNerve.pinchedHom R D y z) _⦋n⦌) :
    (pinchedHomComposition x y z).app _ (pinchedClosedStandardSimplex R D s n, g) =
      (pinchedHomChainMap (D := D) (E := D)
        (x := y) (y := z) (x' := x) (y' := z)
        (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) z))).app _ g := by
  apply pinchedHomStandard_injective x z n
  dsimp only
  rw [pinchedHomComposition_standard x y z, pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (awData (((standardHomPinchedIso y z).inv.app _ g).down).val
    (standardConstant (closedHomEquiv R D _ _ s) n).val).component J k hJ hk =
      (((standardHomPinchedIso x z).inv.app _
        ((pinchedHomChainMap (D := D) (E := D)
          (x := y) (y := z) (x' := x) (y' := z)
          (eHomWhiskerRight (Complex R) s
            (ForgetEnrichment.of (Complex R) z))).app _ g)).down).val.component J k hJ hk
  rw [awData_closed_pre_component, pinchedHomChainMap_standard_component]
  exact (dgGluingHomWhiskerRight_f R D (x := x) (y := y) (z := z) s k
    ((((standardHomPinchedIso y z).inv.app _ g).down).val.component J k hJ hk)).symm

lemma dgGluingPinchedCompositionFamily_closed_pre {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    (g : K ⟶ DGNerve.pinchedHom R D y z) :
    pinchedHomCompositionFamily (SSet.const (pinchedClosedVertex R D s)) g =
      g ≫ pinchedHomChainMap (D := D) (E := D)
        (x := y) (y := z) (x' := x) (y' := z)
        (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) z)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (pinchedHomComposition x y z).app _
      ((SSet.const (X := K) (pinchedClosedVertex R D s)).app _ k, g.app _ k) = _
  rw [pinchedClosedStandardSimplex_const_app, dgGluingPinchedComposition_closed_pre]
  rfl

end SerrePositivity.InfinityCategories
