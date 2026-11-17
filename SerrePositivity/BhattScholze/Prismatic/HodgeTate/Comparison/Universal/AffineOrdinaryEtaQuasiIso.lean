module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryQuasiIso
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineLineOrdinaryBaseHomology

/-!
# 元のηそのものの通常係数拡大の擬同型性

## 概要
指定零延長の表示による検査を、同じ元の通常係数拡大したηへ戻す。

## 方針
元の複体の同型を終域から外す。

## 規約
元のηの型と二つの標準HT実現の等式を保つ。

## 使われ方
HT04.R2の通常被覆像から元の指定完備被覆像の検査への入力。
-/

public noncomputable section
universe u
open CategoryTheory HomologicalComplex
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 明示した終域のHT同型から、同じ元の通常係数拡大したηが擬同型になる。 -/
theorem affineOrdinaryEta_quasiIso
    (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q)
    (hg : Q.generator = (p : B)) (hHT : HodgeTateIsoStatement Q hQ 1)
    (η : affineLineFormalModel P ⟶ affineHTTotalComplex P hP 1)
    (h0 : (affineLineFormalZeroIso P).hom ≫ homologyMap η 0 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 0))
    (h1 : (affineLineFormalOneIso P).hom ≫ homologyMap η 1 =
      ModuleCat.ofHom (affineHTTotalMap P hP 1 1)) :
    QuasiIso (((ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)).map
      ((affineRestrictedComplexFunctor P 1).map η)) := by
  let E := (ModuleCat.extendScalars f.toRingHom).mapHomologicalComplex (.up ℤ)
  let e := E.mapIso (affineOriginalBaseComplexIso P hP 1) ≪≫
    SerrePositivity.mapExtendIso (ModuleCat.extendScalars f.toRingHom)
      (affineBaseComplex P hP 1) ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} B)).mapIso
      (affineAnyOrdinaryComplexIso f hP hQ hg 1)
  have he : affineLineOrdinaryBaseRealization f hP hQ hg η =
      E.map ((affineRestrictedComplexFunctor P 1).map η) ≫ e.hom := by
    simp only [affineLineOrdinaryBaseRealization, Functor.map_comp, e, Iso.trans_hom,
      Functor.mapIso_hom, Category.assoc, E]
    rfl
  have hη := affineLineOrdinaryBaseRealization_quasiIso f hP hQ hg hHT η h0 h1
  rw [he] at hη
  exact (quasiIso_iff_comp_right _ e.hom).mp hη

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
