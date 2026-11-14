module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechAcyclic
public import SerrePositivity.AlgebraicGeometry.CechAdditiveCoefficientComparison
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
概要：増大 Čech の完全性は、係数環の作用の制限でも成り立つ。
方針：制限しても変わらない係数の加法群を、既存の加法的係数比較に渡す。
規約：テンソル底変換ではなく、任意の環準同型に沿う係数制限。
使われ方：大域切断の環上の比較を、射影射の元の基底環上へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X]
variable {R B : Type v} [CommRing R] [CommRing B] (φ : R →+* B)
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} B) {ι : Type} [LinearOrder ι] (U : ι → Opens X)

/-- 係数環を制限しても、増大 Čech の完全性は保たれる。 -/
theorem openCoverCechAcyclic_restrictScalars (h : OpenCoverCechAcyclic P U) :
    OpenCoverCechAcyclic (P ⋙ ModuleCat.restrictScalars φ) U := by
  let D := openCoverCechDiagram P U
  let E := openCoverCechDiagram (P ⋙ ModuleCat.restrictScalars φ) U
  let e : ∀ T, D.obj T ≃+ E.obj T := fun _ ↦ AddEquiv.refl _
  have he : ∀ {T S : Finset ι} (hTS : T ⊆ S) (x : D.obj T),
      e S ((D.map (homOfLE hTS)).hom x) = (E.map (homOfLE hTS)).hom (e T x) := by
    intro T S hTS x
    rfl
  exact {
    injective_zero := fullCechAdditiveCoefficientEquiv_zero_injective D E e he h.injective_zero
    exact := fun k ↦ fullCechAdditiveCoefficientEquiv_exact D E e he k (h.exact k) }

end SerrePositivity.AlgebraicGeometry
