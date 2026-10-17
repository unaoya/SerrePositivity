module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarRepresentable
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleHom
public import SerrePositivity.DifferentialGraded.Module.Yoneda

/-! # 実際の加群Hom係数変更比較とdg Yoneda評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (z : D)

lemma scalarUnitElement_one :
    let := φ.toAlgebra
    (unitElement A' (show ScalarExtension.DGBaseChange φ D from z)).val =
      (1 : A') ⊗ₜ[A] (unitElement A z).val := by
  let := φ.toAlgebra
  change ((ScalarExtension.extension φ).map (eId (Complex A) z)).f 0
    ((ScalarExtension.unitIso φ).inv.f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A'))) = _
  erw [ScalarExtension.sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ]
  rfl

variable [Small.{u} D] (M : RightModule A D)

def scalarModuleYonedaEvaluation :
    moduleHom A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.rightModule φ D (representable A z)) (ScalarExtension.rightModule φ D M) ⟶
      (ScalarExtension.extension φ).obj (M.obj (op z)) :=
  yonedaEvaluateFamily A' (show ScalarExtension.DGBaseChange φ D from z)
    (ScalarExtension.rightModule φ D M)
    (fun y => moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) y.unop)

/-- 実際の加群Hom係数変更比較は、dg Yonedaの単位評価と可換する。 -/
lemma scalarModuleHom_yoneda_square :
    scalarModuleHom φ D (representable A z) M ≫ scalarModuleYonedaEvaluation φ D z M =
      (ScalarExtension.extension φ).map (dgYonedaIso A z M).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (scalarModuleYonedaEvaluation φ D z M).f p
    ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t)) = _
  refine (yonedaEvaluateFamily_apply A' (show ScalarExtension.DGBaseChange φ D from z)
    (ScalarExtension.rightModule φ D M)
    (fun y => moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) y.unop) p
    ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t))).trans ?_
  have hπ := congrArg (fun f => f.f p ((1 : A') ⊗ₜ[A] t))
    (scalarModuleHom_π φ D (representable A z) M z)
  change (moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) z).f p
      ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t)) = _ at hπ
  change ((moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
    (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) z).f p
      ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t))).v 0 p (by omega)
      (unitElement A' (show ScalarExtension.DGBaseChange φ D from z)).val =
    ((ScalarExtension.extension φ).map (dgYonedaIso A z M).hom).f p ((1 : A') ⊗ₜ[A] t)
  rw [hπ, scalarUnitElement_one φ D z]
  erw [ModuleCat.ExtendScalars.map_tmul φ, ScalarExtension.homComparison_apply]
  exact congrArg (fun m => (1 : A') ⊗ₜ[A] m)
    (yonedaEvaluateFamily_apply A z M
      (fun y => moduleHomπ A D (representable A z) M y.unop) p t).symm

end SerrePositivity.DifferentialGraded
