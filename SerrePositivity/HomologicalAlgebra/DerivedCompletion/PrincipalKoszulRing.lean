module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalKoszulUnit

/-! # 実際の一座標Koszul完備化のH⁰の環と普遍性

標準元を保つ比較から得た加群の反射性を、環構造復元の一般定理へ適用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 実際の一座標Koszul完備化の零次ホモロジー。 -/
abbrev PrincipalCompletionH0 (f : R) :=
  (koszulCompletionComplex R (fun _ : Fin 1 ↦ f)).homology 0

/-- 元の加法群・加群と両立する、実際のH⁰上の可換環構造。 -/
@[instance_reducible] def principalCompletionCommRing (f : R) :
    CommRing (PrincipalCompletionH0 R f) :=
  (principalCompletionH0_isCompleteModuleReflection R f).commRing

/-- 元のスカラー作用を保つ、実際のH⁰のR代数構造。 -/
@[instance_reducible] def principalCompletionAlgebra (f : R) :
    letI := principalCompletionCommRing R f; Algebra R (PrincipalCompletionH0 R f) :=
  (principalCompletionH0_isCompleteModuleReflection R f).algebra

/-- 既存のH⁰標準写像を環準同型として実現する。 -/
def principalCompletionUnitRingHom (f : R) :
    letI := principalCompletionCommRing R f; R →+* PrincipalCompletionH0 R f :=
  (principalCompletionH0_isCompleteModuleReflection R f).unitRingHom

/-- 環としての標準写像は、既存のKoszul完備化のH⁰標準写像と一致する。 -/
theorem principalCompletionUnitRingHom_apply (f r : R) :
    principalCompletionUnitRingHom R f r =
      koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f) r :=
  (principalCompletionH0_isCompleteModuleReflection R f).unitRingHom_eq_linearMap
    (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ f)) rfl r

/-- 実際のH⁰は、fについて導来完備なR加群。 -/
theorem principalCompletionH0_isModuleComplete (f : R) :
    IsModuleComplete R f (PrincipalCompletionH0 R f) :=
  (principalCompletionH0_isCompleteModuleReflection R f).isComplete 0

/-- 実際のH⁰から導来完備なR代数への延長は一意。 -/
theorem principalCompletion_existsUnique_algHom (f : R)
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsModuleComplete R f (ModuleCat.of R T)) :
    letI := principalCompletionCommRing R f
    letI := principalCompletionAlgebra R f
    ∃! _g : PrincipalCompletionH0 R f →ₐ[R] T, True :=
  (principalCompletionH0_isCompleteModuleReflection R f).existsUnique_algHom T (fun _ ↦ hT)

/-- 任意の環準同型は、標準写像から導来完備な離散環へ一意に延長する。 -/
theorem principalCompletion_existsUnique_ringHom (f : R)
    (T : Type u) [CommRing T] (g : R →+* T)
    (hT : letI := g.toAlgebra; IsModuleComplete R f (ModuleCat.of R T)) :
    letI := principalCompletionCommRing R f
    ∃! h : PrincipalCompletionH0 R f →+* T,
      h.comp (principalCompletionUnitRingHom R f) = g := by
  let := g.toAlgebra
  let := principalCompletionCommRing R f
  let := principalCompletionAlgebra R f
  obtain ⟨h, _, hu⟩ := principalCompletion_existsUnique_algHom R f T hT
  refine ⟨h.toRingHom, ?_, ?_⟩
  · ext r
    exact h.commutes r
  · intro k hk
    let k' : PrincipalCompletionH0 R f →ₐ[R] T :=
      { k with commutes' := fun r ↦ congrArg (fun m : R →+* T ↦ m r) hk }
    exact congrArg AlgHom.toRingHom (hu k' trivial)

end SerrePositivity.DerivedCompletion
