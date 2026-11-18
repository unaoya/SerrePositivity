module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZero
public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingDerivedComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.OrdinaryHoComposition
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.StrictHomology

/-!
# 導来代数の π₀ と複体の H⁰ の比較

## 概要
Berger–Fresse §1 の π₀ の加群は、忘却した導来複体の H⁰ に自然同型。

## 方針
全厳密代数の上で元の H⁰ と比較し、通常の局所化の充満忠実性で降ろす。

## 規約
既存の導来複体の H⁰ と、基礎環の下の代数の加群忘却を使う。

## 使われ方
BS 著者版 Theorem 6.2 の `pi0_forget` 欄。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

namespace BarrattEccles

open DifferentialGraded

variable (A : Type u) [CommRing A]

/-- The underlying module of the strict H⁰ algebra is the ordinary H⁰ module. -/
def strictPiZero_forgetIso :
    strictPiZero A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A ≅
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) 0 := by
  let e := commAlgCatEquivUnder (CommRingCat.of A)
  let U := forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
    forget₂ (AlgCat.{u} A) (ModuleCat.{u} A)
  have h : homologyAlgebraFunctor A ⋙ U =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) 0 := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact Functor.isoWhiskerLeft (homologyAlgebraFunctor A)
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.unitIso.symm U ≪≫
      Functor.leftUnitor U) ≪≫ eqToIso h

/-- π₀ の加群は忘却した導来複体の H⁰ と自然同型。 -/
def barrattEcclesPi0_forget :
    barrattEcclesPi0 A ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule A ≅
      hoMap (cAlgForgetDerived A) ⋙ cohomologyOnHo A 0 := by
  let L := ordinaryAlgebraHoSource A
  let W := ordinaryAlgebraWeak A
  let Q := algebraCAlgSource A
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)
  let I := ordinaryToHoNerve (operad A).Algebra
  let D := _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A
  let H := cohomologyOnHo A 0
  letI := ordinaryAlgebraHoSource_isLocalization A
  apply (Localization.fullyFaithfulWhiskeringLeft L W (ModuleCat A)).preimageIso
  let a := (hoMapCompIso Q (cAlgForgetDerived A)).symm ≪≫
    (algebraCAlgSource_underlyingDerivedIso A).toNatIso ≪≫ hoMapCompIso (nerveMap U) D
  have b : L ⋙ hoMap (cAlgForgetDerived A) ⋙ H ≅
      (I ⋙ hoMap (nerveMap U)) ⋙ hoMap D ⋙ H := by
    simpa only [Functor.assoc, L, ordinaryAlgebraHoSource, I, Q] using
      Functor.isoWhiskerLeft I (Functor.isoWhiskerRight a H)
  have c : (I ⋙ hoMap (nerveMap U)) ⋙ hoMap D ⋙ H ≅
      U ⋙ HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) 0 := by
    exact Functor.isoWhiskerRight (ordinaryToHoNerve_naturalIso U) _ ≪≫
      Functor.isoWhiskerLeft U (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSourceHomologyIso A 0)
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (barrattEcclesPi0_sourceIso A) _ ≪≫
    strictPiZero_forgetIso A ≪≫ c.symm ≪≫ b.symm

end BarrattEccles
end SerrePositivity.EInfinity
