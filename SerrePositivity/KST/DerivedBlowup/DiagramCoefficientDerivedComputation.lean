module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientTransitionSquare
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の指定係数比較の導来成分計算。
方針：二つの標準導来制限合成同型を実加群上で計算する。
規約：通常加群で指定した同型の局所化像との一致を保持する。
使われ方：canonical な比較の可換式を全導来対象へ移す入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
namespace SerrePositivity.KST.DerivedBlowup
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

/-- 概要：指定導来評価比較の実加群上の成分は指定通常比較の像。
方針：二つの標準合成同型の局所化公式を合成する。
規約：KST §3.1。使われ方：canonical な可換式の導来化。 -/
theorem diagramCoefficientDerivedEvaluationIso_hom_app_Q (i : J) (M : AllDiagramModules G) :
    (diagramCoefficientDerivedEvaluationIso α i).hom.app
      ((moduleToDerived R (DiagramModuleCoefficientObject G)ᵒᵖ).obj M) =
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      ((diagramCoefficientModuleEvaluationIso α i).hom.app M) := by
  change (transitionDerivedRestrictionCompIso _ _ _ _).hom.app _ ≫
    (transitionDerivedRestrictionCompIso _ _ _ _).inv.app _ = _
  rw [transitionDerivedRestrictionCompIso_hom_app_Q,
    transitionDerivedRestrictionCompIso_inv_app_Q, ← CategoryTheory.Functor.map_comp]
  rfl

omit [DecidableLE J] [Small.{u} (DiagramModuleCoefficientObject F)]
  [Small.{u} (DiagramModuleCoefficientObject G)] in
/-- 概要：指定導来遷移四角形の実加群上の成分は通常四角形の像。
方針：二つの標準合成同型の局所化公式を合成する。
規約：KST §3.1・Lemma 3.6。使われ方：可換式の行先の同型を計算する。 -/
theorem diagramCoefficientDerivedTransitionIso_hom_app_Q {i j : J} (h : i ≤ j)
    (M : ModuleCategory R (AlgebraVertex (G.obj j))ᵒᵖ) :
    (diagramCoefficientDerivedTransitionIso α h).hom.app
      ((moduleToDerived R (AlgebraVertex (G.obj j))ᵒᵖ).obj M) =
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      ((diagramCoefficientModuleTransitionIso α h).hom.app M) := by
  change (transitionDerivedRestrictionCompIso _ _ _ _).hom.app _ ≫
    (transitionDerivedRestrictionCompIso _ _ _ _).inv.app _ = _
  rw [transitionDerivedRestrictionCompIso_hom_app_Q,
    transitionDerivedRestrictionCompIso_inv_app_Q, ← CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.KST.DerivedBlowup
