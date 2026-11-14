module

public import SerrePositivity.EInfinity.PowerOperation.MayNormalizedSourceComparison
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroForget

/-!
# BE の零次環とホモロジーの源での比較

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
def mayModuleHomologySourceIso (k : Type u) [CommRing k] (i : ℤ) :
    ordinaryAlgebraHoSource k ⋙
      hoMap (cAlgForgetDerived k) ⋙ cohomologyOnHo k i ≅
        Operad.Algebra.forget (operad k) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) i := by
  let A := k
  let L := ordinaryAlgebraHoSource A
  let Q := algebraCAlgSource A
  let U := Operad.Algebra.forget (operad A)
  let I := ordinaryToHoNerve (operad A).Algebra
  let D := ComplexLimits.complexOrdinaryDerivedSource A
  let H := cohomologyOnHo A i
  let a := (hoMapCompIso Q (cAlgForgetDerived A)).symm ≪≫
    (algebraCAlgSource_underlyingDerivedIso A).toNatIso ≪≫ hoMapCompIso (nerveMap U) D
  have b : L ⋙ hoMap (cAlgForgetDerived A) ⋙ H ≅
      (I ⋙ hoMap (nerveMap U)) ⋙ hoMap D ⋙ H := by
    simpa only [Functor.assoc, L, ordinaryAlgebraHoSource, I, Q] using
      Functor.isoWhiskerLeft I (Functor.isoWhiskerRight a H)
  have c : (I ⋙ hoMap (nerveMap U)) ⋙ hoMap D ⋙ H ≅
      U ⋙ HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i := by
    exact Functor.isoWhiskerRight (ordinaryToHoNerve_naturalIso U) _ ≪≫
      Functor.isoWhiskerLeft U (ComplexLimits.complexOrdinaryDerivedSourceHomologyIso A i)
  exact b ≪≫ c

/-- 台の加法群へ忘れて得る比較は、同じ指定された源の比較。 -/
lemma mayModuleHomologySourceIso_forget (k : Type u) [CommRing k] (n : ℤ) :
    Functor.isoWhiskerRight (mayModuleHomologySourceIso k (-n))
      (forget₂ (ModuleCat k) AddCommGrpCat) = mayNormalizedHomologySourceIso k n := rfl

/-- 零次環の源の同型と、その台の指定ホモロジーとの合成。 -/
def mayPiZeroSourceRight (k : Type u) [CommRing k] :
    ordinaryAlgebraHoSource k ⋙ barrattEcclesPi0 k ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule k ≅
        Operad.Algebra.forget (operad k) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) 0 :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (barrattEcclesPi0_sourceIso k) _ ≪≫ strictPiZero_forgetIso k

lemma mayPiZeroForget_as_preimage (k : Type u) [CommRing k] :
    barrattEcclesPi0_forget k =
      (let _ := ordinaryAlgebraHoSource_isLocalization k
       (Localization.fullyFaithfulWhiskeringLeft (ordinaryAlgebraHoSource k)
         (ordinaryAlgebraWeak k) (ModuleCat k)).preimageIso
           (mayPiZeroSourceRight k ≪≫ (mayModuleHomologySourceIso k 0).symm)) := by
  rfl

/-- 忘却の比較を源へ引き戻し、同じ指定ホモロジー比較を続けると環の源の比較。 -/
lemma mayPiZeroForget_source_square (k : Type u) [CommRing k] :
    Functor.whiskerLeft (ordinaryAlgebraHoSource k) (barrattEcclesPi0_forget k).hom ≫
      (mayModuleHomologySourceIso k 0).hom = (mayPiZeroSourceRight k).hom := by
  let _ := ordinaryAlgebraHoSource_isLocalization k
  let ff := Localization.fullyFaithfulWhiskeringLeft (ordinaryAlgebraHoSource k)
    (ordinaryAlgebraWeak k) (ModuleCat k)
  have hh : Functor.whiskerLeft (ordinaryAlgebraHoSource k) (barrattEcclesPi0_forget k).hom =
      (mayPiZeroSourceRight k ≪≫ (mayModuleHomologySourceIso k 0).symm).hom := by
    rw [mayPiZeroForget_as_preimage]
    exact ff.map_preimage _
  rw [hh]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma mayPiZeroForget_source_apply (k : Type u) [CommRing k] (X : (operad k).Algebra)
    (a : ((barrattEcclesPi0 k).obj ((ordinaryAlgebraHoSource k).obj X)).right) :
    (mayModuleHomologySourceIso k 0).hom.app X
      ((barrattEcclesPi0_forget k).hom.app ((ordinaryAlgebraHoSource k).obj X) a) =
        (mayPiZeroSourceRight k).hom.app X a :=
  congrArg (fun η => η.app X a) (mayPiZeroForget_source_square k)

local instance mayPiZeroSourceCommRing {k : Type u} [CommRing k] (X : (operad k).Algebra) :
    CommRing ((Operad.Algebra.forget (operad k) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat k) (.up ℤ) 0).obj X) := homologyCommRing X

/-- 厳密な零次環の台の比較は、同じ H⁰ の積を保つ。 -/
lemma mayStrictPiZeroForget_pow (k : Type u) [CommRing k] (X : (operad k).Algebra)
    (a : ((strictPiZero k).obj X).right) (m : ℕ) :
    (strictPiZero_forgetIso k).hom.app X (a ^ m) =
      ((strictPiZero_forgetIso k).hom.app X a : X.carrier.homology 0) ^ m := by
  rfl

lemma mayPiZeroSourceRight_pow (k : Type u) [CommRing k] (X : (operad k).Algebra)
    (a : ((barrattEcclesPi0 k).obj ((ordinaryAlgebraHoSource k).obj X)).right) (m : ℕ) :
    (mayPiZeroSourceRight k).hom.app X (a ^ m) =
      ((mayPiZeroSourceRight k).hom.app X a : X.carrier.homology 0) ^ m := by
  change (strictPiZero_forgetIso k).hom.app X
    (((barrattEcclesPi0_sourceIso k).hom.app X).right.hom (a ^ m)) = _
  rw [map_pow, mayStrictPiZeroForget_pow]
  rfl

end SerrePositivity.EInfinity.PowerOperation
