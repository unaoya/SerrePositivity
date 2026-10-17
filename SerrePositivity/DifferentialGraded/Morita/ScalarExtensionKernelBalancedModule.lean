module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelBalanced

/-! # 係数変更したkernel作用の全Hom自然な加群比較

比較を係数制限側で構成し、既存の加群係数変更随伴で戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
  ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : Bimodule A E D) (M : RightModule A D)

def scalarKernelBalancedUnitComponent (e : E) :
    BalancedTensor.obj A D M (P.leftAt e) ⟶
      (restriction φ).obj (BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D M) ((scalarKernel φ D E P).leftAt e)) :=
  (adjunction φ).unit.app _ ≫ (restriction φ).map (scalarKernelBalancedValueIso φ D E P M e).hom

lemma scalarKernelBalancedUnitComponent_element (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op d)).X r) (v : (P.value e d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    (scalarKernelBalancedUnitComponent φ D E P M e).f n
        (BalancedTensor.element A D M (P.leftAt e) d m v h) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
        ((scalarKernel φ D E P).leftAt e) d ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) h := by
  let := φ.toAlgebra
  exact scalarKernelBalancedValueIso_element_one φ D E P M e d m v h

lemma scalarKernelBalancedUnit_naturality (x y : Eᵒᵖ) :
    ((kernelTensor A D E P).obj M).map x y ≫
        homPostcompose (((kernelTensor A D E P).obj M).obj x)
          (scalarKernelBalancedUnitComponent φ D E P M y.unop) =
      (rightRestriction φ E ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).obj (rightModule φ D M))).map x y ≫
        homPrecompose (scalarKernelBalancedUnitComponent φ D E P M x.unop)
          ((rightRestriction φ E ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
            (scalarKernel φ D E P)).obj (rightModule φ D M))).obj y) := by
  let := φ.toAlgebra
  apply BalancedTensor.homMap_post_pre_eq A D M (P.leftAt x.unop)
  intro p f d r s i n hi hn m v
  change (scalarKernelBalancedUnitComponent φ D E P M y.unop).f n
      (moduleAction A ((kernelTensor A D E P).obj M) (x := x) (y := y) f
        (BalancedTensor.element A D M (P.leftAt x.unop) d m v hi) hn) =
    moduleAction A (rightRestriction φ E
      ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
        (rightModule φ D M))) (x := x) (y := y) f
      ((scalarKernelBalancedUnitComponent φ D E P M x.unop).f i
        (BalancedTensor.element A D M (P.leftAt x.unop) d m v hi)) hn
  erw [BimoduleTensor.compose_rightAction_element A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D)) x y d M hi rfl hn f m v]
  dsimp only [Bimodule.rightAt, DGFunctor.id]
  simp only [Units.smul_def, map_zsmul]
  have hy := scalarKernelBalancedUnitComponent_element φ D E P M y.unop d
    (r := r) (s := s + p) (n := n) m
    (moduleAction A (P.rightAt d) (x := x) (y := y) f v (rfl : s + p = s + p))
    (by omega : r + (s + p) = n)
  have hx := scalarKernelBalancedUnitComponent_element φ D E P M x.unop d
    (r := r) (s := s) (n := i) m v hi
  have hl := congrArg (fun z => (p * r).negOnePow.val • z) hy
  have hr := congrArg (fun z => moduleAction A
    (rightRestriction φ E
      ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
        (rightModule φ D M))) (x := x) (y := y) f z hn) hx
  refine hl.trans (Eq.trans ?_ hr.symm)
  have hrest := rightRestriction_action φ E
    ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
      (rightModule φ D M)) x y p i n hn f
    (BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
      ((scalarKernel φ D E P).leftAt x.unop) d ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) hi)
  erw [hrest]
  erw [BimoduleTensor.compose_rightAction_element A' (DGBaseChange φ E) (DGBaseChange φ D)
    (RightModule A' (DGBaseChange φ D)) (scalarKernel φ D E P)
    (DGFunctor.id (RightModule A' (DGBaseChange φ D))) x y d (rightModule φ D M)
    hi rfl hn ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v)]
  erw [rightModule_action φ E (P.rightAt d) x y p s (s + p) rfl f v]
  rfl

def scalarKernelBalancedUnit :
    ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj M) ⟶
      (ScalarExtension.moduleRestriction φ E).obj
        (ForgetEnrichment.of (Complex A')
          ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
            (scalarKernel φ D E P)).obj (rightModule φ D M))) :=
  moduleMorphismMk A E
    (M := (kernelTensor A D E P).obj M)
    (N := rightRestriction φ E
      ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
        (rightModule φ D M)))
    (fun x => scalarKernelBalancedUnitComponent φ D E P M x.unop)
    (scalarKernelBalancedUnit_naturality φ D E P M)

lemma scalarKernelBalancedUnit_eval (e : E) :
    (moduleEvaluation A E e).map (scalarKernelBalancedUnit φ D E P M) =
      scalarKernelBalancedUnitComponent φ D E P M e :=
  moduleMorphismMk_eval A E _ _ e

/-- 随伴により戻した、実際の係数変更加群圏の比較射。 -/
def scalarKernelBalancedMap :
    (moduleExtension φ E).obj (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj M)) ⟶
      ForgetEnrichment.of (Complex A')
        ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj (rightModule φ D M)) :=
  ((moduleAdjunction φ E).homEquiv _ _).symm (scalarKernelBalancedUnit φ D E P M)

lemma scalarKernelBalancedMap_eval (e : E) :
    (moduleEvaluation A' (DGBaseChange φ E) e).map (scalarKernelBalancedMap φ D E P M) =
      (scalarKernelBalancedValueIso φ D E P M e).hom := by
  rw [scalarKernelBalancedMap, Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp]
  change (moduleEvaluation A' (DGBaseChange φ E) e).map
      ((moduleExtension φ E).map (scalarKernelBalancedUnit φ D E P M)) ≫
      (moduleEvaluation A' (DGBaseChange φ E) e).map (moduleCounitApp φ E _) = _
  rw [moduleExtension_eval, scalarKernelBalancedUnit_eval, moduleCounitApp_eval]
  change (extension φ).map
      ((adjunction φ).unit.app (BalancedTensor.obj A D M (P.leftAt e)) ≫
        (restriction φ).map (scalarKernelBalancedValueIso φ D E P M e).hom) ≫
      (adjunction φ).counit.app _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have h := (adjunction φ).counit.naturality (scalarKernelBalancedValueIso φ D E P M e).hom
  simp only [Functor.comp_map, Functor.id_map] at h
  erw [h]
  rw [← Category.assoc]
  erw [(adjunction φ).left_triangle_components (BalancedTensor.obj A D M (P.leftAt e))]
  exact Category.id_comp _

/-- 任意の環準同型に対する、kernel作用のunderived係数変更の実際の加群同型。 -/
def scalarKernelBalancedIso :
    (moduleExtension φ E).obj (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj M)) ≅
      ForgetEnrichment.of (Complex A')
        ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj (rightModule φ D M)) := by
  have : IsIso (scalarKernelBalancedMap φ D E P M) :=
    moduleIsIso_of_evaluations A' (DGBaseChange φ E) _ (fun e => by
      rw [scalarKernelBalancedMap_eval]
      infer_instance)
  exact asIso (scalarKernelBalancedMap φ D E P M)

lemma scalarKernelBalancedIso_hom_eval (e : E) :
    (moduleEvaluation A' (DGBaseChange φ E) e).map (scalarKernelBalancedIso φ D E P M).hom =
      (scalarKernelBalancedValueIso φ D E P M e).hom :=
  scalarKernelBalancedMap_eval φ D E P M e

end SerrePositivity.DifferentialGraded.Morita
