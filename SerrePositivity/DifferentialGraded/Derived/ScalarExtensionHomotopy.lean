module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.ResolutionFunctorChoice

/-! # 非 flat な係数拡大と加群ホモトピー

標準 cylinder の射影だけを反転して境界を同一視する。
任意の擬同型を underived 係数拡大が保存するとは仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 標準 cylinder の射影は任意の係数変更後も擬同型。 -/
lemma moduleExtension_cylinder_quasiIso (M : ModuleCategory A D) :
    moduleQuasiIso A' (DGBaseChange φ D)
      ((moduleExtension φ D).map (modulePrecylinder A D M).π) := by
  intro x
  rw [moduleExtension_eval]
  change QuasiIso ((extension φ).map ((moduleEvaluation A D x).map
    (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom)))
  rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval,
    CategoryTheory.Functor.map_comp]
  have : QuasiIso ((extension φ).map
      (cylinder.π (𝟙_ (Complex A)) ⊗ₘ
        𝟙 ((ForgetEnrichment.to (Complex A) M).obj (Opposite.op x)))) :=
    ((ModuleCat.extendScalars φ).mapHomotopyEquiv
      (tensorIntervalHomotopyEquiv A
        ((ForgetEnrichment.to (Complex A) M).obj (Opposite.op x)))).quasiIso_hom
  infer_instance

/-- 係数拡大後の主導来圏では、元の全 dg 自然な境界が等しくなる。 -/
lemma moduleExtension_equalizes_boundary {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A D) f g) :
    (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map f) =
      (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map g) := by
  let F := moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D)
  let P := modulePrecylinder A D M
  let H := moduleCylinderLeftHomotopy A D f g h
  let e := @asIso (DerivedModuleCategory A' (DGBaseChange φ D)) _ _ _ (F.map P.π)
    (moduleToDerived_inverts A' (DGBaseChange φ D) _
      (moduleExtension_cylinder_quasiIso φ D M))
  have hi : F.map P.i₀ = F.map P.i₁ := by
    have hs : F.map P.i₀ ≫ e.hom = F.map P.i₁ ≫ e.hom := by
      change F.map P.i₀ ≫ F.map P.π = F.map P.i₁ ≫ F.map P.π
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, P.i₀_π, P.i₁_π]
    have hc := congrArg (fun k => k ≫ e.inv) hs
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hc
  change F.map f = F.map g
  calc
    F.map f = F.map (P.i₀ ≫ H.h) := congrArg F.map H.h₀.symm
    _ = F.map P.i₀ ≫ F.map H.h := F.map_comp _ _
    _ = F.map P.i₁ ≫ F.map H.h := congrArg (fun k => k ≫ F.map H.h) hi
    _ = F.map g := (F.map_comp _ _).symm.trans (congrArg F.map H.h₁)

/-- 任意の係数変更を K(D) から係数変更後の主導来圏へ送る。 -/
def moduleExtensionHomotopyToDerived : ModuleHomotopyCategory A D ⥤
    DerivedModuleCategory A' (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift _
    (moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D))
    (fun _ _ f g h => moduleExtension_equalizes_boundary φ D f g h)

lemma moduleExtensionHomotopyToDerived_fac :
    moduleToHomotopy A D ⋙ moduleExtensionHomotopyToDerived φ D =
      moduleExtension φ D ⋙ moduleToDerived A' (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

lemma moduleExtension_map_eq_of_homotopy {M N : ModuleCategory A D} (f g : M ⟶ N)
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map f) =
      (moduleToDerived A' (DGBaseChange φ D)).map ((moduleExtension φ D).map g) :=
  congrArg (moduleExtensionHomotopyToDerived φ D).map h

end SerrePositivity.DifferentialGraded.ScalarExtension
