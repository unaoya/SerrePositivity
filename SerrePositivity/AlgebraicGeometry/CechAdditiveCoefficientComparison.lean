module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Exact.Basic

/-!
概要：異なる係数環の切断の加法的な同定に沿って、増大 Čech の完全性を移す。
方針：各交叉の加法群の同型を直積し、制限との可換性から余境界の可換性を得る。
規約：この輸送は完全性だけを扱い、係数環の線形構造を同一視しない。
使われ方：アフィン座標での準連接層の計算を、元のスキームの係数へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R A ι : Type*} [CommRing R] [CommRing A] [DecidableEq ι]
variable (D : Finset ι ⥤ ModuleCat R) (E : Finset ι ⥤ ModuleCat A)
variable (e : ∀ T, D.obj T ≃+ E.obj T)
variable (he : ∀ {T S : Finset ι} (h : T ⊆ S) (x : D.obj T),
  e S ((D.map (homOfLE h)).hom x) = (E.map (homOfLE h)).hom (e T x))

/-- 各交叉の加法的な比較による Čech 項の加法群の同型。 -/
def fullCechAdditiveCoefficientEquiv (k : ℕ) :
    FullCechCochains D k ≃+ FullCechCochains E k :=
  AddEquiv.piCongrRight fun t ↦ e (cechTupleSupport t)

include he in
/-- 係数の制限と可換な加法的比較は、Čech 微分と可換。 -/
theorem fullCechAdditiveCoefficientEquiv_differential (k : ℕ)
    (x : FullCechCochains D k) :
    fullCechAdditiveCoefficientEquiv D E e (k + 1) (fullCechDifferential D k x) =
      fullCechDifferential E k (fullCechAdditiveCoefficientEquiv D E e k x) := by
  funext t
  change e (cechTupleSupport t) (fullCechDifferential D k x t) =
    fullCechDifferential E k (fullCechAdditiveCoefficientEquiv D E e k x) t
  simp only [fullCechDifferential_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (((-1 : ℤ) ^ i.val) • ·)
    (he (cechTupleSupport_face_subset t i) (x (t ∘ i.succAbove)))

include he in
/-- 加法的係数比較によって、増大項の単射性を移す。 -/
theorem fullCechAdditiveCoefficientEquiv_zero_injective
    (h : Function.Injective (fullCechDifferential D 0)) :
    Function.Injective (fullCechDifferential E 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (fullCechAdditiveCoefficientEquiv D E e 0).surjective x
  obtain ⟨b, rfl⟩ := (fullCechAdditiveCoefficientEquiv D E e 0).surjective y
  congr 1
  apply h
  apply (fullCechAdditiveCoefficientEquiv D E e 1).injective
  rw [fullCechAdditiveCoefficientEquiv_differential D E e he,
    fullCechAdditiveCoefficientEquiv_differential D E e he]
  exact hxy

include he in
/-- 加法的係数比較によって、増大 Čech の完全性を移す。 -/
theorem fullCechAdditiveCoefficientEquiv_exact (k : ℕ)
    (h : Function.Exact (fullCechDifferential D k) (fullCechDifferential D (k + 1))) :
    Function.Exact (fullCechDifferential E k) (fullCechDifferential E (k + 1)) := by
  apply (Function.Exact.iff_of_ladder_addEquiv
    (fullCechAdditiveCoefficientEquiv D E e k)
    (fullCechAdditiveCoefficientEquiv D E e (k + 1))
    (fullCechAdditiveCoefficientEquiv D E e (k + 2))
    (f₁₂ := (fullCechDifferential D k).toAddMonoidHom)
    (f₂₃ := (fullCechDifferential D (k + 1)).toAddMonoidHom)
    (g₁₂ := (fullCechDifferential E k).toAddMonoidHom)
    (g₂₃ := (fullCechDifferential E (k + 1)).toAddMonoidHom) ?_ ?_).mpr h
  · apply AddMonoidHom.ext
    intro x
    exact (fullCechAdditiveCoefficientEquiv_differential D E e he k x).symm
  · apply AddMonoidHom.ext
    intro x
    exact (fullCechAdditiveCoefficientEquiv_differential D E e he (k + 1) x).symm

end SerrePositivity.AlgebraicGeometry
