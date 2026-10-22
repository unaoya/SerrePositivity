module
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionFunctorTriangle
public import SerrePositivity.InfinityCategories.Derived.Gluing.CompositionTriangleEvaluation

/-! 具体的な native 三角形は curry 後も全二単体族を回収し、対角表示の等式輸送でも変わらない。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgGluingFunctorTriangleCast_evaluation {K X : SSet.{u}} {a b c : K ⟶ X}
    {P : Type w} (H : P → SSet.Homotopy a c) {f g : P} (h : f = g)
    {l : SSet.Homotopy a b} {r : SSet.Homotopy b c}
    (T : FunctorCompositionTriangle l r (H f)) :
    dgGluingCompositionTriangleEvaluation
        (Eq.mp (congrArg (fun q => FunctorCompositionTriangle l r (H q)) h) T) =
      dgGluingCompositionTriangleEvaluation T := by
  subst g
  rfl

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  {K X : SSet.{max u v}} {x y z : D}
  (f : K ⟶ DGNerve.pinchedHom R D x y) (g : K ⟶ DGNerve.pinchedHom R D y z)
  (q : dgNerve R D ⟶ X)

lemma dgGluingDGCompositionFunctorTriangle_evaluate :
    dgGluingCompositionTriangleEvaluation (dgGluingDGCompositionFunctorTriangle R D f g q) =
      dgGluingDGCompositionTriangleFamilyPost R D f g q := by
  change (β_ (Δ[2] : SSet.{max u v}) K).hom ≫
    uncurry (curry ((β_ K (Δ[2] : SSet.{max u v})).hom ≫
      dgGluingDGCompositionTriangleFamilyPost R D f g q)) = _
  rw [uncurry_curry, SymmetricCategory.symmetry_assoc]

end SerrePositivity.InfinityCategories
