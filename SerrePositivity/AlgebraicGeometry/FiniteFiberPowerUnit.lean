module

public import SerrePositivity.AlgebraicGeometry.FiniteFiberPowerSucc

/-!
概要：一個の有限ファイバー冪と元の対象との、基底への射を保つ同型。
方針：既存の π・lift の法則と Fin 1 の一意性を使う。
規約：既存の wide pullback を対象とし、増大項への同じ射を保つ。
使われ方：Čech nerve の各次数の射影表示の帰納の最初。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {X S : C} (f : X ⟶ S)
local notation "a" => (fun _ : Fin 1 ↦ f)

/-- 一個の有限ファイバー冪の射影は、元の対象との同型。 -/
def finiteFiberPowerZeroIso : widePullback S (fun _ : Fin 1 ↦ X) a ≅ X where
  hom := WidePullback.π a 0
  inv := WidePullback.lift f (fun _ ↦ 𝟙 X) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, WidePullback.lift_base,
        WidePullback.π_arrow, Category.id_comp]
  inv_hom_id := by simp only [WidePullback.lift_π]

/-- 一個の冪との同型は、元の基底への射を保つ。 -/
theorem finiteFiberPowerZeroIso_hom_base :
    (finiteFiberPowerZeroIso f).hom ≫ f = WidePullback.base a :=
  WidePullback.π_arrow a 0

end SerrePositivity.AlgebraicGeometry
