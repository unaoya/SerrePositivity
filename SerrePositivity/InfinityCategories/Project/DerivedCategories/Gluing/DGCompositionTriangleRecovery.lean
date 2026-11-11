module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionFunctorTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CompositionTriangleEvaluation

/-! 具体的な native 三角形は curry 後も全二単体族を回収し、対角表示の等式輸送でも変わらない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial

lemma dgGluingFunctorTriangleCast_evaluation {K X : SSet.{u}} {a b c : K ⟶ X}
    {P : Type w} (H : P → SSet.Homotopy a c) {f g : P} (h : f = g)
    {l : SSet.Homotopy a b} {r : SSet.Homotopy b c}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (H f)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation
        (Eq.mp (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (H q)) h) T) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation T := by
  subst g
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  {K X : SSet.{max u v}} {x y z : D}
  (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z)
  (q : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D ⟶ X)

lemma dgGluingDGCompositionFunctorTriangle_evaluate :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCompositionTriangleEvaluation (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionFunctorTriangle R D f g q) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamilyPost R D f g q := by
  change (β_ (Δ[2] : SSet.{max u v}) K).hom ≫
    uncurry (curry ((β_ K (Δ[2] : SSet.{max u v})).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamilyPost R D f g q)) = _
  rw [uncurry_curry, SymmetricCategory.symmetry_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
