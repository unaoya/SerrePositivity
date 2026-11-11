module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroForget
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyRestrictionOperations

/-!
# 導来代数の π₀ と係数制限

## 概要
HA §3.2.2 の係数制限と、Berger–Fresse §1 の H⁰ を可換環として比較する。

## 方針
厳密代数上で積・単位を比較し、同じ局所化源から自然同型を降ろす。

## 規約
基礎環の下の圏での比較であり、元の構造準同型を保つ。

## 使われ方
M13 の `pi0_restrict` 欄。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory DifferentialGraded
open SerrePositivity.InfinityCategories

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

private def strictPiZeroRestrictComponent (X : (operad T).Algebra) :
    (strictPiZero S).obj ((coefficientRestriction f).obj X) ≅
      (restrictRingAlgebra f).obj ((strictPiZero T).obj X) := by
  let Y := (coefficientRestriction f).obj X
  let M := ModuleCat.restrictScalars f
  let e : Y.carrier.homology 0 ≅ M.obj (X.carrier.homology 0) :=
    (exactCochainHomologyIso M 0).app X.carrier
  let g : (homologyCommAlgebra Y) →+* (homologyCommAlgebra X) :=
    { toFun := e.hom
      map_zero' := map_zero e.hom.hom
      map_add' := map_add e.hom.hom
      map_one' := restrictedHomologyOne f X
      map_mul' := restrictedHomologyProduct f X }
  let h : homologyCommAlgebra Y ≃+* homologyCommAlgebra X :=
    RingEquiv.ofBijective g (show Function.Bijective g from e.toLinearEquiv.bijective)
  refine Under.isoMk h.toCommRingCatIso ?_
  apply ConcreteCategory.hom_ext
  intro r
  let := homologyCommRing Y
  let := homologyAlgebra Y
  let := homologyCommRing X
  let := homologyAlgebra X
  change e.hom (algebraMap S (Y.carrier.homology 0) r) =
    algebraMap T (X.carrier.homology 0) (f r)
  rw [homologyAlgebra_algebraMap Y, homologyAlgebra_algebraMap X]
  calc
    _ = r • e.hom (homologyOne Y) := e.hom.hom.map_smul r _
    _ = (f r) • homologyOne X := by
      rw [show e.hom (homologyOne Y) = homologyOne X from restrictedHomologyOne f X]
      rfl

/-- The usual H⁰ comparison on strict Barratt–Eccles algebras. -/
@[no_expose]
def strictPiZero_restrictIso :
    coefficientRestriction f ⋙ strictPiZero S ≅ strictPiZero T ⋙ restrictRingAlgebra f := by
  refine NatIso.ofComponents (strictPiZeroRestrictComponent f) ?_
  intro X Y g
  apply Under.UnderMorphism.ext
  apply ConcreteCategory.hom_ext
  intro x
  let M := ModuleCat.restrictScalars f
  let E := exactCochainHomologyIso M 0
  simp only [Under.comp_right, CommRingCat.comp_apply]
  unfold strictPiZeroRestrictComponent
  let g' := (coefficientRestriction f).map g
  change (E.hom.app Y.carrier) (HomologicalComplex.homologyMap g'.hom 0 x) =
    HomologicalComplex.homologyMap g.hom 0 ((E.hom.app X.carrier) x)
  exact ConcreteCategory.congr_hom (E.hom.naturality g.hom) x

/-- The degree-zero ring functor commutes with derived restriction of scalars. -/
def barrattEcclesPi0_restrict :
    hoMap (barrattEcclesRestrict f) ⋙ barrattEcclesPi0 S ≅
      barrattEcclesPi0 T ⋙ restrictRingAlgebra f := by
  let L := ordinaryAlgebraHoSource T
  let W := ordinaryAlgebraWeak T
  let F := coefficientRestriction f
  let I := ordinaryToHoNerve (operad T).Algebra
  let Q := algebraCAlgSource T
  let Q' := algebraCAlgSource S
  let P := barrattEcclesPi0 S
  letI := ordinaryAlgebraHoSource_isLocalization T
  apply (Localization.fullyFaithfulWhiskeringLeft L W (RingAlgebra S)).preimageIso
  let a := (hoMapCompIso Q (barrattEcclesRestrict f)).symm ≪≫
    (barrattEcclesRestrict_sourceIso f).toNatIso ≪≫ hoMapCompIso (nerveMap F) Q'
  have b : L ⋙ hoMap (barrattEcclesRestrict f) ⋙ P ≅ F ⋙ ordinaryAlgebraHoSource S ⋙ P := by
    simpa only [Functor.assoc, L, ordinaryAlgebraHoSource] using
      (Functor.isoWhiskerLeft I (Functor.isoWhiskerRight a P) ≪≫
        (by simpa only [Functor.assoc] using
          Functor.isoWhiskerRight (ordinaryToHoNerve_naturalIso F) (hoMap Q' ⋙ P)))
  exact b ≪≫ Functor.isoWhiskerLeft F (barrattEcclesPi0_sourceIso S) ≪≫
    strictPiZero_restrictIso f ≪≫
    Functor.isoWhiskerRight (barrattEcclesPi0_sourceIso T).symm _ ≪≫
    Functor.associator _ _ _

end SerrePositivity.EInfinity.BarrattEccles
