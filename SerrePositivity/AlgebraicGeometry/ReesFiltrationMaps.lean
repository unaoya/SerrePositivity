module

public import SerrePositivity.AlgebraicGeometry.ReesFiltrationModule
public import Mathlib.Algebra.Exact.Basic

/-!
概要：フィルトレーションを保つ写像は Rees 加群の写像を与える。
方針：多項式加群の係数ごとの写像に制限し、各次数の持ち上げを有限和で足す。
規約：完全性は各次数成分で仮定する。
使われ方：Rees 加群から Čech の短完全列を作り、形式関数の自然な写像へ渡す。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum

variable {R M N P : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]
variable {I : Ideal R} (F : I.Filtration M) (G : I.Filtration N) (H : I.Filtration P)

/-- フィルトレーションを保つ線形写像から得る Rees 環上の線形写像。 -/
def reesFiltrationMap (f : M →ₗ[R] N) (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n) :
    F.submodule →ₗ[reesAlgebra I] G.submodule where
  toFun p := ⟨PolynomialModule.map R f p.val, fun n ↦ by
    change f (p.val.coeff n) ∈ G.N n
    exact hf n _ (p.property n)⟩
  map_add' x y := Subtype.ext ((PolynomialModule.map R f).map_add x.val y.val)
  map_smul' r x := by
    apply Subtype.ext
    change PolynomialModule.map R f (r.val • x.val) = r.val • PolynomialModule.map R f x.val
    simpa using PolynomialModule.map_smul (R' := R) f r.val x.val

/-- Rees 加群の写像は係数ごとに元の写像を適用する。 -/
theorem reesFiltrationMap_coeff (f : M →ₗ[R] N)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n) (p : F.submodule) (n : ℕ) :
    (reesFiltrationMap F G f hf p).val.coeff n = f (p.val.coeff n) := rfl

/-- Rees 加群の写像は単項式と可換。 -/
theorem reesFiltrationMap_single (f : M →ₗ[R] N)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n) (n : ℕ) (m : F.N n) :
    reesFiltrationMap F G f hf (reesFiltrationSingle F n m) =
      reesFiltrationSingle G n ⟨f m.val, hf n _ m.property⟩ := by
  apply Subtype.ext
  exact PolynomialModule.map_lsingle (R' := R) f n m.val

/-- 恒等写像が与える Rees 加群の写像。 -/
theorem reesFiltrationMap_id :
    reesFiltrationMap F F LinearMap.id (fun _ _ h ↦ h) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  ext n
  rfl

/-- Rees 加群の写像は合成を保つ。 -/
theorem reesFiltrationMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n)
    (hg : ∀ n, ∀ m ∈ G.N n, g m ∈ H.N n) :
    (reesFiltrationMap G H g hg).comp (reesFiltrationMap F G f hf) =
      reesFiltrationMap F H (g.comp f) (fun n m hm ↦ hg n _ (hf n m hm)) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  ext n
  rfl

/-- Rees 加群の写像と、次数成分の直和から足す写像の可換性。 -/
theorem reesFiltrationMap_assemble (f : M →ₗ[R] N)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n) (z : ⨁ n, F.N n) :
    reesFiltrationMap F G f hf (reesFiltrationAssemble F z) =
      reesFiltrationAssemble G (DirectSum.lmap (fun n ↦
        (f.comp (F.N n).subtype).codRestrict (G.N n) (fun m ↦ hf n m.val m.property)) z) := by
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  ext n
  rw [reesFiltrationMap_coeff, reesFiltrationAssemble_coeff, reesFiltrationAssemble_coeff]
  rfl

/-- 元の写像が単射なら、フィルトレーションを保つ Rees 加群の写像も単射。 -/
theorem reesFiltrationMap_injective (f : M →ₗ[R] N)
    (hf : ∀ n, ∀ m ∈ F.N n, f m ∈ G.N n) (hinj : Function.Injective f) :
    Function.Injective (reesFiltrationMap F G f hf) := by
  intro x y h
  apply Subtype.ext
  apply PolynomialModule.coeff_injective
  ext n
  apply hinj
  have hc := congrArg (fun p : G.submodule ↦ p.val.coeff n) h
  simpa only [reesFiltrationMap_coeff] using hc

end SerrePositivity.AlgebraicGeometry
