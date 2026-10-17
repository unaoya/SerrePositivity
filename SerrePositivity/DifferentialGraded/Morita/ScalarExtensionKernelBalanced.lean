module
public import SerrePositivity.DifferentialGraded.Morita.ScalarExtensionKernelFunctor
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-! # kernel作用のunderived係数変更を全Hom作用へ束ねる

複体の係数変更同型を左評価の比較と合成する。
全Hom自然性は係数変更・制限随伴を使い、元の係数環のcoend生成元上で検証する。
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

lemma scalarBalancedIso_element_one (M : RightModule A D) (N : LeftModule A D)
    (d : D) {r s n : ℤ} (m : (M.obj (op d)).X r) (v : (N.obj d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    (balancedIso φ D M N).hom.f n ((1 : A') ⊗ₜ[A] BalancedTensor.element A D M N d m v h) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) d
        ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) h := by
  let := φ.toAlgebra
  have he := congrArg (fun k => k.f n
    ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op d)) (N.obj d) r s n h (m ⊗ₜ[A] v)))
      (balancedIso_ι φ D M N d)
  change (balancedIso φ D M N).hom.f n
      (((extension φ).map (BalancedTensor.ι A D M N d)).f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op d)) (N.obj d) r s n h (m ⊗ₜ[A] v))) =
    (BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) d).f n
      ((tensorIso φ (M.obj (op d)) (N.obj d)).hom.f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op d)) (N.obj d) r s n h (m ⊗ₜ[A] v))) at he
  erw [ModuleCat.ExtendScalars.map_tmul φ,
    cochainTensorBaseChangeIso_apply_ι φ (M.obj (op d)) (N.obj d) r s n h] at he
  exact he

lemma scalarBalancedIso_map_element_one (M : RightModule A D) (N : LeftModule A D)
    (N' : LeftModuleCategory A' (DGBaseChange φ D))
    (g : ForgetEnrichment.of (Complex A') (leftModule φ D N) ⟶ N')
    (d : D) {r s n : ℤ} (m : (M.obj (op d)).X r) (v : (N.obj d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    ((BalancedTensor.leftTensorFunctor A' (DGBaseChange φ D) (rightModule φ D M)).map g).f n
        ((balancedIso φ D M N).hom.f n
          ((1 : A') ⊗ₜ[A] BalancedTensor.element A D M N d m v h)) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
        (ForgetEnrichment.to (Complex A') N') d ((1 : A') ⊗ₜ[A] m)
          (((leftModuleEvaluation A' (DGBaseChange φ D) d).map g).f s ((1 : A') ⊗ₜ[A] v)) h := by
  let := φ.toAlgebra
  rw [scalarBalancedIso_element_one φ D M N d m v h]
  dsimp only [BalancedTensor.leftTensorFunctor]
  erw [BalancedTensor.map_element]
  erw [CategoryTheory.Functor.map_id]
  rfl

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : Bimodule A E D) (M : RightModule A D)

/-- 全Hom付き左評価の同一視を、閉零左加群の同型として読む。 -/
def scalarKernelLeftValueIso (e : E) :
    ForgetEnrichment.of (Complex A') ((scalarKernel φ D E P).leftAt e) ≅
      ForgetEnrichment.of (Complex A') (leftModule φ D (P.leftAt e)) :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A')) (scalarKernel_leftAt φ D E P e))

def scalarKernelBalancedValueIso (e : E) :
    (extension φ).obj (BalancedTensor.obj A D M (P.leftAt e)) ≅
      BalancedTensor.obj A' (DGBaseChange φ D) (rightModule φ D M)
        ((scalarKernel φ D E P).leftAt e) :=
  balancedIso φ D M (P.leftAt e) ≪≫
    ((BalancedTensor.leftTensorFunctor A' (DGBaseChange φ D) (rightModule φ D M)).mapIso
      (scalarKernelLeftValueIso φ D E P e)).symm

lemma scalarKernelLeftValueIso_inv_eval (e : E) (d : D) :
    (leftModuleEvaluation A' (DGBaseChange φ D) d).map
        (scalarKernelLeftValueIso φ D E P e).inv = 𝟙 _ := by
  simp only [scalarKernelLeftValueIso, eqToIso.inv, eqToHom_map, eqToHom_refl]

lemma scalarKernelLeftValueIso_inv_eval_one (e : E) (d : D) (s : ℤ)
    (v : (P.value e d).X s) :
    let := φ.toAlgebra
    (((leftModuleEvaluation A' (DGBaseChange φ D) d).map
      (scalarKernelLeftValueIso φ D E P e).inv).f s)
        ((1 : A') ⊗ₜ[A] v) = (1 : A') ⊗ₜ[A] v := by
  let := φ.toAlgebra
  rw [scalarKernelLeftValueIso_inv_eval φ D E P e d]
  rfl

lemma scalarKernelBalancedValueIso_element_one (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op d)).X r) (v : (P.value e d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    (scalarKernelBalancedValueIso φ D E P M e).hom.f n
        ((1 : A') ⊗ₜ[A] BalancedTensor.element A D M (P.leftAt e) d m v h) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
        ((scalarKernel φ D E P).leftAt e) d ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) h := by
  let := φ.toAlgebra
  have he := scalarBalancedIso_map_element_one φ D M (P.leftAt e)
    (ForgetEnrichment.of (Complex A') ((scalarKernel φ D E P).leftAt e))
    (scalarKernelLeftValueIso φ D E P e).inv d m v h
  rw [scalarKernelLeftValueIso_inv_eval_one φ D E P e d s v] at he
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  exact he

end SerrePositivity.DifferentialGraded.Morita
