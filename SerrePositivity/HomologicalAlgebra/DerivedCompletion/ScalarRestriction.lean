module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulRing

/-! # 導来完備性の係数制限と別座標の保存

列作用の判定を使い、環準同型に沿う作用の比較を証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- 代数写像に沿う係数制限は、対応する元についての導来完備性を保ち、反映する。 -/
theorem isModuleComplete_algebraMap_iff (f : R) (M : Type u)
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] :
    IsModuleComplete S (algebraMap R S f) (ModuleCat.of S M) ↔
      IsModuleComplete R f (ModuleCat.of R M) := by
  rw [isModuleComplete_iff_recurrence_bijective, isModuleComplete_iff_recurrence_bijective]
  have he : (fun x : ℕ → M ↦ adicRecurrenceMap (algebraMap R S f) x) =
      fun x : ℕ → M ↦ adicRecurrenceMap f x := by
    funext x n
    simp [adicRecurrenceMap]
  exact (congrArg Function.Bijective he).to_iff

/-- 別の元に関する主元反射は、既にある導来完備性を保つ。 -/
theorem principalReflection_isModuleComplete_of_other (f : R) (d : S)
    (hS : IsModuleComplete R f (ModuleCat.of R S)) :
    let := Module.compHom (PrincipalReflectionModule S d) (algebraMap R S)
    IsModuleComplete R f (ModuleCat.of R (PrincipalReflectionModule S d)) := by
  let := Module.compHom (PrincipalReflectionModule S d) (algebraMap R S)
  have hP := isModuleComplete_pi R f (fun _ : ℕ ↦ ModuleCat.of R S) (fun _ ↦ hS)
  let g := (principalReflectionRelation S d).restrictScalars R
  have hQ := isModuleComplete_coker R f g hP hP
  let e : ((ℕ → S) ⧸ g.range) ≃ₗ[R] PrincipalReflectionModule S d :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          have he : ((algebraMap R S r) • x : ℕ → S) = r • x := by
            ext n
            simp [Algebra.smul_def]
          exact congrArg (fun z : ℕ → S ↦ (principalReflectionRelation S d).range.mkQ z) he.symm }
  exact isModuleComplete_of_linearEquiv R f (ModuleCat.of R ((ℕ → S) ⧸ g.range))
    (ModuleCat.of R (PrincipalReflectionModule S d)) e hQ

/-- 実際の主元Koszul完備化のH⁰も、別の元についての導来完備性を保つ。 -/
theorem principalCompletionH0_isModuleComplete_of_other (f : R) (d : S)
    (hS : IsModuleComplete R f (ModuleCat.of R S)) :
    letI := Module.compHom (PrincipalCompletionH0 S d) (algebraMap R S)
    IsModuleComplete R f (ModuleCat.of R (PrincipalCompletionH0 S d)) := by
  let _ : Module R (PrincipalCompletionH0 S d) :=
    Module.compHom (PrincipalCompletionH0 S d) (algebraMap R S)
  let _ : Module R (PrincipalReflectionModule S d) :=
    Module.compHom (PrincipalReflectionModule S d) (algebraMap R S)
  have hQ := principalReflection_isModuleComplete_of_other R S f d hS
  let e : PrincipalCompletionH0 S d ≃ₗ[R] PrincipalReflectionModule S d :=
    { toFun := principalCompletionH0Equiv S d
      invFun := (principalCompletionH0Equiv S d).symm
      left_inv := (principalCompletionH0Equiv S d).left_inv
      right_inv := (principalCompletionH0Equiv S d).right_inv
      map_add' := (principalCompletionH0Equiv S d).map_add
      map_smul' := fun r x ↦ (principalCompletionH0Equiv S d).map_smul (algebraMap R S r) x }
  exact isModuleComplete_of_linearEquiv R f
    (ModuleCat.of R (PrincipalReflectionModule S d))
    (ModuleCat.of R (PrincipalCompletionH0 S d)) e.symm hQ

end SerrePositivity.DerivedCompletion
