module

public import SerrePositivity.HomologicalAlgebra.CochainCompleteDetection
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic

/-!
# 導来完備環の有限関係商

## 概要
導来主元完備な環を有限個の関係で割った環は同じ主元について導来完備。
## 方針
有限 Koszul 複体の完備性と零次ホモロジーの通常商との比較を使う。
## 規約
BS 著者版 Proposition 7.10 の T の完備性への入力。関係列の正則性は不要。
## 使われ方
根付き基底の通常の有限商と、drafts の実 H⁰ 完備化の比較。
-/

public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R]

/-- 概要：有限関係の商は係数環の導来主元完備性を保つ。
方針：完備な有限 Koszul 複体の零次ホモロジーを通常商へ移す。
規約：BS 著者版 Proposition 7.10。正則性・Noether 性・非零性は不要。
使われ方：有限 T の通常商が既に導来 p 完備であること。 -/
theorem isModuleComplete_finiteRelationQuotient (a : R)
    (hR : IsModuleComplete R a (ModuleCat.of R R)) {r : ℕ} (z : Fin r → R) :
    IsModuleComplete R a (ModuleCat.of R (R ⧸ Ideal.span (Set.range z))) := by
  let K0 := (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R)
  have hK : IsComplete R a (DerivedCategory.Q.obj (koszulComplex z)) := by
    rw [← koszulComplexOn_single]
    exact koszulComplexOn_isComplete a z K0 hR
  have hH := isComplete_homology_isModuleComplete R a (DerivedCategory.Q.obj (koszulComplex z)) hK 0
  let e := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) 0).app (koszulComplex z)
  have hH' := isModuleComplete_of_linearEquiv R a _ _ e.toLinearEquiv hH
  exact isModuleComplete_of_linearEquiv R a _ _
    (koszulComplex_homology_zero_equiv z).some hH'

/-- 実主元 p 完備化の環は、自身の p 作用について導来完備。 -/
theorem principalCompletionRing_self_complete (p : ℕ) :
    let H := principalCompletionRingCat p (CommRingCat.of R)
    IsModuleComplete H (p : H) (ModuleCat.of H H) := by
  let H := principalCompletionRingCat p (CommRingCat.of R)
  letI := (principalCompletionRingCatUnit p (CommRingCat.of R)).hom.toAlgebra
  letI : Module R H := Algebra.toModule
  have h : IsModuleComplete R (p : R) (ModuleCat.of R H) :=
    principalCompletion_isModuleComplete_unit (R := R) (p : R)
  have h' := (isModuleComplete_algebraMap_iff R H (p : R) H).mpr h
  simpa only [map_natCast] using h'

/-- 概要：導来完備な離散環では主元完備化の単位は環同型。
方針：完備化の実際の環としての一意延長を両方向に使う。
規約：BS 著者版 Proposition 7.10 の完備化比較。零環も含む。
使われ方：drafts の completionRing と既に完備な有限商の照合。 -/
def principalCompletionEquivOfComplete (a : R)
    (hR : IsModuleComplete R a (ModuleCat.of R R)) :
    letI := principalCompletionCommRing R a
    PrincipalCompletionH0 R a ≃+* R := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let i : R →ₐ[R] PrincipalCompletionH0 R a := Algebra.ofId R _
  let g := principalCompletionLiftAlgHom R a R hR
  have hgi : g.comp i = AlgHom.id R R := by ext
  have hig : i.comp g = AlgHom.id R (PrincipalCompletionH0 R a) :=
    (principalCompletion_existsUnique_algHom R a (PrincipalCompletionH0 R a)
      (principalCompletionH0_isModuleComplete R a)).unique trivial trivial
  exact (AlgEquiv.ofAlgHom g i hgi hig).toRingEquiv

/-- 完備環への同型は、元の完備化単位を恒等射へ戻す。 -/
theorem principalCompletionEquivOfComplete_comp_unit (a : R)
    (hR : IsModuleComplete R a (ModuleCat.of R R)) :
    letI := principalCompletionCommRing R a
    (principalCompletionEquivOfComplete R a hR).toRingHom.comp
      (principalCompletionUnitRingHom R a) = RingHom.id R := by
  letI := principalCompletionCommRing R a
  apply RingHom.ext
  intro x
  exact (principalCompletionEquivOfComplete R a hR).apply_symm_apply x

end SerrePositivity.DerivedCompletion
