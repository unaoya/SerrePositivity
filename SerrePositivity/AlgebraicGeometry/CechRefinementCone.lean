module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：非負次数の複体の射の mapping cone を、負一の項から自然数で添字付けする。
方針：第零項を元の複体の第零項とし、以後は二つの項の直積にする。
規約：導来関手の層コホモロジーは使わず、加群の複体の計算を行う。
使われ方：共通アフィン細分の Čech 射の cone に、二重複体の完全性判定を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (A B : CochainComplex (ModuleCat.{u} R) ℕ)

/-- 自然数で添字付けした cone の項。 -/
def cechRefinementConeTerm : ℕ → ModuleCat.{u} R
  | 0 => A.X 0
  | n + 1 => ModuleCat.of R (B.X n × A.X (n + 1))

/-- 負一から移した cone の微分。 -/
def cechRefinementConeDifferential (f : A ⟶ B) :
    ∀ n, cechRefinementConeTerm A B n →ₗ[R] cechRefinementConeTerm A B (n + 1)
  | 0 => (f.f 0).hom.prod (-(A.d 0 1).hom)
  | n + 1 =>
      (((B.d n (n + 1)).hom.comp (LinearMap.fst R _ _)) +
        ((f.f (n + 1)).hom.comp (LinearMap.snd R _ _))).prod
          (-((A.d (n + 1) (n + 2)).hom.comp (LinearMap.snd R _ _)))

/-- この添字付けでも cone の微分の二乗は零。 -/
theorem cechRefinementConeDifferential_squared (f : A ⟶ B) (n : ℕ) :
    (cechRefinementConeDifferential A B f (n + 1)).comp
      (cechRefinementConeDifferential A B f n) = 0 := by
  have hf (i : ℕ) (x : A.X i) :
      (B.d i (i + 1)).hom ((f.f i).hom x) =
        (f.f (i + 1)).hom ((A.d i (i + 1)).hom x) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun a ↦ a.hom x) (f.comm i (i + 1))
  have hdA (i : ℕ) (x : A.X i) :
      (A.d (i + 1) (i + 2)).hom ((A.d i (i + 1)).hom x) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun a ↦ a.hom x) (A.d_comp_d i (i + 1) (i + 2))
  have hdB (i : ℕ) (x : B.X i) :
      (B.d (i + 1) (i + 2)).hom ((B.d i (i + 1)).hom x) = 0 := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun a ↦ a.hom x) (B.d_comp_d i (i + 1) (i + 2))
  apply LinearMap.ext
  intro x
  cases n with
  | zero =>
    change ((B.d 0 1).hom ((f.f 0).hom x) + (f.f 1).hom (-(A.d 0 1).hom x),
      -(A.d 1 2).hom (-(A.d 0 1).hom x)) = (0, 0)
    simp only [map_neg, hf, hdA, add_neg_cancel, neg_zero]
  | succ n =>
    change ((B.d (n + 1) (n + 2)).hom
        ((B.d n (n + 1)).hom x.1 + (f.f (n + 1)).hom x.2) +
          (f.f (n + 2)).hom (-(A.d (n + 1) (n + 2)).hom x.2),
      -(A.d (n + 2) (n + 3)).hom (-(A.d (n + 1) (n + 2)).hom x.2)) = (0, 0)
    simp only [map_add, map_neg, hdB, hf, hdA, zero_add, add_neg_cancel, neg_zero]

/-- 共通アフィン細分の射の完全性を測る、自然数添字の cone。 -/
def cechRefinementCone (f : A ⟶ B) : CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of (cechRefinementConeTerm A B)
    (fun n ↦ ModuleCat.ofHom (cechRefinementConeDifferential A B f n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact cechRefinementConeDifferential_squared A B f n)

end SerrePositivity.AlgebraicGeometry
