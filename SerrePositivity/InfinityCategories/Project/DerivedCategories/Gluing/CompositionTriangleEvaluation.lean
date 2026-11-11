module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-! 同じ関手圏内三角形を、三辺を保って実二単体とパラメーターの族へ評価する。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {U V W : K ⟶ X}
  {l : SSet.Homotopy U V} {r : SSet.Homotopy V W} {d : SSet.Homotopy U W}
  (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d)

def dgGluingCompositionTriangleEvaluation : (Δ[2] : SSet.{u}) ⊗ K ⟶ X :=
  (β_ (Δ[2] : SSet.{u}) K).hom ≫ uncurry T.diagram

lemma dgGluingCompositionTriangleEvaluation_face {A B : K ⟶ X}
    (i : Fin 3) (H : SSet.Homotopy A B)
    (h : stdSimplex.δ i ≫ T.diagram = curry H.h) :
    (stdSimplex.δ i ▷ K) ≫ dgGluingCompositionTriangleEvaluation T =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
  rw [dgGluingCompositionTriangleEvaluation, BraidedCategory.braiding_naturality_left_assoc,
    ← uncurry_natural_left, h, uncurry_curry]

lemma dgGluingCompositionTriangleEvaluation_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingCompositionTriangleEvaluation T =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ r.h :=
  dgGluingCompositionTriangleEvaluation_face T 0 r T.face_zero

lemma dgGluingCompositionTriangleEvaluation_one :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ dgGluingCompositionTriangleEvaluation T =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ d.h :=
  dgGluingCompositionTriangleEvaluation_face T 1 d T.face_one

lemma dgGluingCompositionTriangleEvaluation_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingCompositionTriangleEvaluation T =
      (β_ (Δ[1] : SSet.{u}) K).hom ≫ l.h :=
  dgGluingCompositionTriangleEvaluation_face T 2 l T.face_two

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
