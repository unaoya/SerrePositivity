module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Exact.Basic

/-!
概要：係数図式の直積と Čech の項・完全性を比較する。
方針：二つのタプルの積の順序を交換し、各成分で前像を選ぶ。
規約：完全性の議論では直積の添字の有限性は不要。
使われ方：共通細分の二重 Čech 図式で、各交叉上の完全性を行の完全性にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R ι σ : Type*} [CommRing R] [DecidableEq ι]
variable (D : σ → Finset ι ⥤ ModuleCat R)

/-- 係数図式の成分ごとの直積。 -/
def fullCechProductCoefficientDiagram : Finset ι ⥤ ModuleCat R where
  obj T := ModuleCat.of R (∀ s, (D s).obj T)
  map h := ModuleCat.ofHom (LinearMap.pi fun s ↦
    ((D s).map h).hom.comp (LinearMap.proj s))
  map_id T := by
    ext x s
    exact congrArg (fun f ↦ f.hom (x s)) ((D s).map_id T)
  map_comp f g := by
    ext x s
    exact congrArg (fun h ↦ h.hom (x s)) ((D s).map_comp f g)

/-- 係数の直積と Čech 項の直積の交換。 -/
def fullCechProductCochainsEquiv (k : ℕ) :
    FullCechCochains (fullCechProductCoefficientDiagram D) k ≃ₗ[R]
      ∀ s, FullCechCochains (D s) k where
  toFun a s t := a t s
  invFun a t s := a s t
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 直積の交換は Čech 微分と成分ごとに可換。 -/
theorem fullCechProductDifferential_apply (k : ℕ)
    (a : FullCechCochains (fullCechProductCoefficientDiagram D) k)
    (t : Fin (k + 1) → ι) (s : σ) :
    fullCechDifferential (fullCechProductCoefficientDiagram D) k a t s =
      fullCechDifferential (D s) k (fun t ↦ a t s) t := by
  rw [fullCechDifferential_apply (D s) k]
  have h := congrFun (fullCechDifferential_apply (fullCechProductCoefficientDiagram D) k a t) s
  simpa only [Finset.sum_apply, Pi.smul_apply, fullCechProductCoefficientDiagram,
    ModuleCat.hom_ofHom, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply] using h

/-- 各係数図式の増大項の微分が単射なら、直積の微分も単射。 -/
theorem fullCechProduct_zero_injective
    (h : ∀ s, Function.Injective (fullCechDifferential (D s) 0)) :
    Function.Injective (fullCechDifferential (fullCechProductCoefficientDiagram D) 0) := by
  intro x y hxy
  have hs (s : σ) : (fun t ↦ x t s) = (fun t ↦ y t s) := by
    apply h s
    funext t
    rw [← fullCechProductDifferential_apply D 0 x t s,
      ← fullCechProductDifferential_apply D 0 y t s]
    exact congrFun (congrFun hxy t) s
  funext t s
  exact congrFun (hs s) t

/-- 各係数図式の増大 Čech が完全なら、直積も完全。 -/
theorem fullCechProduct_exact (k : ℕ)
    (h : ∀ s, Function.Exact (fullCechDifferential (D s) k)
      (fullCechDifferential (D s) (k + 1))) :
    Function.Exact (fullCechDifferential (fullCechProductCoefficientDiagram D) k)
      (fullCechDifferential (fullCechProductCoefficientDiagram D) (k + 1)) := by
  intro x
  constructor
  · intro hx
    have hs (s : σ) : ∃ y, fullCechDifferential (D s) k y = (fun t ↦ x t s) := by
      apply (h s _).mp
      funext t
      rw [← fullCechProductDifferential_apply D (k + 1) x t s]
      exact congrFun (congrFun hx t) s
    choose y hy using hs
    refine ⟨fun t s ↦ y s t, ?_⟩
    funext t s
    exact (fullCechProductDifferential_apply D k (fun t s ↦ y s t) t s).trans
      (congrFun (hy s) t)
  · rintro ⟨y, rfl⟩
    funext t s
    rw [fullCechProductDifferential_apply]
    have hy : (fun u ↦ fullCechDifferential (fullCechProductCoefficientDiagram D) k y u s) =
        fullCechDifferential (D s) k (fun u ↦ y u s) := by
      funext u
      exact fullCechProductDifferential_apply D k y u s
    rw [hy]
    exact congrFun ((h s _).mpr ⟨fun u ↦ y u s, rfl⟩) t

end SerrePositivity.AlgebraicGeometry
