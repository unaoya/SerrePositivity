module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.RightModuleComparison
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionHomotopy

/-! # 積dg圏のH⁰から主導来kernelへの非flatな係数変更

標準cylinderの射影だけを反転してH⁰へ降ろす。
通常の係数変更が任意のkernel擬同型を保存するとは仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite HomologicalComplex ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 積上の射の係数変更の擬同型性を、同じ値を持つ係数変更kernelへ運ぶ。 -/
lemma scalarKernelProduct_quasiIso
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ} (f : M ⟶ N)
    (hf : moduleQuasiIso A' (DGBaseChange φ (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)
      ((moduleExtension φ (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).map f)) :
    BimoduleCategory.quasiIso A' (DGBaseChange φ E) (DGBaseChange φ D)
      ((scalarKernelFunctor φ D E).map ((rightModuleBimoduleEquivalence A E D).functor.map f)) := by
  intro e d
  erw [scalarKernelMap_value φ D E ((rightModuleBimoduleEquivalence A E D).functor.map f) e d]
  let α := rightModuleBimoduleEvaluationIso A E D e d
  have hq : QuasiIso ((extension φ).map
      ((moduleEvaluation A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ (op (op e, d))).map f)) := by
    simpa only [moduleExtension_eval] using hf (op (op e, d))
  have hn := congrArg (extension φ).map (α.hom.naturality f)
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp] at hn
  have ht : QuasiIso ((extension φ).map
      ((BimoduleCategory.valueEvaluation A E D e d).map
        ((rightModuleBimoduleEquivalence A E D).functor.map f)) ≫
      ((extension φ).mapIso (α.app N)).hom) := by
    erw [hn]
    infer_instance
  exact quasiIso_of_comp_right _ ((extension φ).mapIso (α.app N)).hom

lemma scalarKernelProduct_cylinder_quasiIso
    (M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ) :
    BimoduleCategory.quasiIso A' (DGBaseChange φ E) (DGBaseChange φ D)
      ((scalarKernelFunctor φ D E).map
        ((rightModuleBimoduleEquivalence A E D).functor.map
          (modulePrecylinder A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M).π)) :=
  scalarKernelProduct_quasiIso φ D E _
    (moduleExtension_cylinder_quasiIso φ (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M)

/-- 積上の全dg自然な境界は、係数変更kernelの主局所化で等しくなる。 -/
lemma scalarKernelProduct_equalizes_boundary
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ) f g) :
    (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
        ((scalarKernelFunctor φ D E).map ((rightModuleBimoduleEquivalence A E D).functor.map f)) =
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
        ((scalarKernelFunctor φ D E).map
          ((rightModuleBimoduleEquivalence A E D).functor.map g)) := by
  let F := (rightModuleBimoduleEquivalence A E D).functor ⋙ scalarKernelFunctor φ D E ⋙
    bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)
  let P := modulePrecylinder A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M
  let H := moduleCylinderLeftHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ f g h
  have he : IsIso (F.map P.π) := bimoduleToDerived_inverts A'
    (DGBaseChange φ E) (DGBaseChange φ D) _ (scalarKernelProduct_cylinder_quasiIso φ D E M)
  let e := @asIso (DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D))
    _ _ _ (F.map P.π) he
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

/-- 積dg圏の主H⁰から係数変更後の主導来kernelへの実際の関手。 -/
def scalarKernelProductHomotopyToDerived :
    ModuleHomotopyCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ ⥤
      DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift _
    ((rightModuleBimoduleEquivalence A E D).functor ⋙ scalarKernelFunctor φ D E ⋙
      bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D))
    (fun _ _ f g h => scalarKernelProduct_equalizes_boundary φ D E f g h)

lemma scalarKernelProductHomotopyToDerived_fac :
    moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ ⋙
        scalarKernelProductHomotopyToDerived φ D E =
      (rightModuleBimoduleEquivalence A E D).functor ⋙ scalarKernelFunctor φ D E ⋙
        bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- 積上のH⁰同型を、係数変更した実際のkernel対象間の同型として読む。 -/
def scalarKernelProductHomotopyMapIso
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ}
    (e : (moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).obj M ≅
      (moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).obj N) :
    (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj ((rightModuleBimoduleEquivalence A E D).functor.obj M)) ≅
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj ((rightModuleBimoduleEquivalence A E D).functor.obj N)) :=
  (scalarKernelProductHomotopyToDerived φ D E).mapIso e

end SerrePositivity.DifferentialGraded.Morita
