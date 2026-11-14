module

public import SerrePositivity.EInfinity.PowerOperation.MayNormalizedNaturalTransformation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroForget

/-!
# 全次数の BE ホモロジーの局所化源での比較

May, Proposition 2.3 の P⁰ を CAlg のホモトピー圏へ降ろすための補助。
既存の全厳密代数の忘却比較と全次数の複体ホモロジー比較を合成する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.BarrattEccles
open scoped Simplicial

/-- ホモトピー圏の忘却後のホモロジーを全厳密代数へ引き戻した自然比較。 -/
def mayNormalizedHomologySourceIso (k : Type u) [CommRing k] (n : ℤ) :
    ordinaryAlgebraHoSource k ⋙
      hoMap (cAlgForgetDerived k) ⋙ additiveCohomologyOnHo k (-n) ≅
        mayNormalizedStrictHomology k n := by
  let A := k
  let L := ordinaryAlgebraHoSource A
  let Q := algebraCAlgSource A
  let U := Operad.Algebra.forget (operad A)
  let I := ordinaryToHoNerve (operad A).Algebra
  let D := ComplexLimits.complexOrdinaryDerivedSource A
  let H := cohomologyOnHo A (-n)
  let V := forget₂ (ModuleCat A) AddCommGrpCat
  let a := (hoMapCompIso Q (cAlgForgetDerived A)).symm ≪≫
    (algebraCAlgSource_underlyingDerivedIso A).toNatIso ≪≫ hoMapCompIso (nerveMap U) D
  have b : L ⋙ hoMap (cAlgForgetDerived A) ⋙ H ≅
      (I ⋙ hoMap (nerveMap U)) ⋙ hoMap D ⋙ H := by
    simpa only [Functor.assoc, L, ordinaryAlgebraHoSource, I, Q] using
      Functor.isoWhiskerLeft I (Functor.isoWhiskerRight a H)
  have c : (I ⋙ hoMap (nerveMap U)) ⋙ hoMap D ⋙ H ≅
      U ⋙ HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) (-n) := by
    exact Functor.isoWhiskerRight (ordinaryToHoNerve_naturalIso U) _ ≪≫
      Functor.isoWhiskerLeft U (ComplexLimits.complexOrdinaryDerivedSourceHomologyIso A (-n))
  exact Functor.isoWhiskerRight (b ≪≫ c) V

end SerrePositivity.EInfinity.PowerOperation
