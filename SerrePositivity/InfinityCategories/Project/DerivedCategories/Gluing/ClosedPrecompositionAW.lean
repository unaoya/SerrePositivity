module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedPrecompositionComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedClosedStandardConstant

/-! 閉 augmentation との AW 前合成は、対象圏の小ささなしに元の豊穣前合成と一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

lemma dgGluingPinchedComposition_closed_pre {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    {n : ℕ} (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition x y z).app _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex R D s n, g) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := D) (E := D)
        (x := y) (y := z) (x' := x) (y' := z)
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z))).app _ g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomStandard_injective x z n
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition_standard x y z, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex_coordinates]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv.app _ g).down).val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv R D _ _ s) n).val).component J k hJ hk =
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x z).inv.app _
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := D) (E := D)
          (x := y) (y := z) (x' := x) (y' := z)
          (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s
            (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z))).app _ g)).down).val.component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_pre_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_standard_component]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomWhiskerRight_f R D (x := x) (y := y) (z := z) s k
    ((((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso y z).inv.app _ g).down).val.component J k hJ hk)).symm

lemma dgGluingPinchedCompositionFamily_closed_pre {K : SSet.{max u v}} {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R D s)) g =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := D) (E := D)
        (x := y) (y := z) (x' := x) (y' := z)
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomComposition x y z).app _
      ((SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R D s)).app _ k, g.app _ k) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedStandardSimplex_const_app, dgGluingPinchedComposition_closed_pre]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
