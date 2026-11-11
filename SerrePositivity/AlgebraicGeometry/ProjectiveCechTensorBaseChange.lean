module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
概要：有限被覆の全タプル Čech 複体と、実際のテンソル底変換を比較する。
方針：各項の有限積とテンソル積を交換し、交代和の余境界と可換と示す。
規約：環準同型による extendScalars を使い、この複体の比較には平坦性を仮定しない。
使われ方：射影 Čech コホモロジーの flat な底変換への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct ChangeOfRings
universe u
variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- 実際のテンソル底変換は、加群の射の加法を保つ。 -/
local instance projectiveCechTensorExtendAdditive : (ModuleCat.extendScalars φ).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      change b ⊗ₜ[R,φ] (f.hom m + g.hom m) =
        b ⊗ₜ[R,φ] f.hom m + b ⊗ₜ[R,φ] g.hom m
      exact TensorProduct.tmul_add b (f.hom m) (g.hom m)
    | add x y hx hy => simp only [map_add, hx, hy]

variable (D : Finset ι ⥤ ModuleCat.{u} R)

/-- Čech の各項の有限積と、実際のテンソル底変換との交換同型。 -/
def projectiveCechTensorCochainsIso (k : ℕ) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (FullCechCochains D k)) ≅
      ModuleCat.of B (FullCechCochains (D ⋙ ModuleCat.extendScalars φ) k) := by
  letI := φ.toAlgebra
  exact (TensorProduct.piRight R B B (fun t : Fin k → ι ↦ D.obj (cechTupleSupport t))).toModuleIso

/-- 各項のテンソル比較は、純テンソルをタプルごとに評価する。 -/
theorem projectiveCechTensorCochainsIso_tmul (k : ℕ) (b : B) (a : FullCechCochains D k) :
    (projectiveCechTensorCochainsIso φ D k).hom (b ⊗ₜ[R,φ] a) =
      fun t ↦ b ⊗ₜ[R,φ] a t := rfl

/-- テンソル積と有限積の比較は、Čech の交代和の余境界と可換。 -/
theorem projectiveCechTensorCochainsIso_differential (k : ℕ) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom (fullCechDifferential D k)) ≫
        (projectiveCechTensorCochainsIso φ D (k + 1)).hom =
      (projectiveCechTensorCochainsIso φ D k).hom ≫
        ModuleCat.ofHom (fullCechDifferential (D ⋙ ModuleCat.extendScalars φ) k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
    change (projectiveCechTensorCochainsIso φ D (k + 1)).hom
        (b ⊗ₜ[R,φ] (fullCechDifferential D k a)) =
      fullCechDifferential (D ⋙ ModuleCat.extendScalars φ) k
        ((projectiveCechTensorCochainsIso φ D k).hom (b ⊗ₜ[R,φ] a))
    rw [projectiveCechTensorCochainsIso_tmul, projectiveCechTensorCochainsIso_tmul]
    funext t
    simp only [fullCechDifferential_apply, TensorProduct.tmul_sum, Functor.comp_map]
    apply Finset.sum_congr rfl
    intro i _
    change b ⊗ₜ[R,φ] (((-1 : ℤ) ^ i.val) •
        (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom (a (t ∘ i.succAbove))) =
      ((-1 : ℤ) ^ i.val) • (b ⊗ₜ[R,φ]
        (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom (a (t ∘ i.succAbove)))
    exact map_zsmul (TensorProduct.mk R
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of B B))
      (D.obj (cechTupleSupport t)) b) _ _
  | add x y hx hy => simp only [map_add, hx, hy]

/-- 有限被覆の全タプル Čech 複体は、実際のテンソル底変換と交換する。 -/
def projectiveCechTensorComplexIso :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℕ)).obj (fullCechComplex D) ≅
      fullCechComplex (D ⋙ ModuleCat.extendScalars φ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ projectiveCechTensorCochainsIso φ D (q + 1)) (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      simpa only [Functor.mapHomologicalComplex_obj_d, fullCechComplex, CochainComplex.of_d]
        using (projectiveCechTensorCochainsIso_differential φ D (i + 1)).symm)

end SerrePositivity.AlgebraicGeometry
