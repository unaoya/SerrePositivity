module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.CoverCompletionCoordinates
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.NativeModelComparisonNaturality

/-!
# 元の完備導来被覆と元の指定半自由模型の自然同型

## 概要
元の完備導来係数拡大を、同じ指定半自由増大の元の被覆像へ移す。

## 方針
元の模型同型の自然性と、像の座標から(p,p)への元の単位を保つ同型を合成する。

## 規約
元の複体のK-flat性を仮定せず、同じ指定分解を使う。

## 使われ方
HT04.R2の正方形を型つき一覧の完備導来関手の型で読む。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DifferentialGraded DifferentialGraded.ScalarExtension DerivedCompletion HTComparisonTotal HTComparisonResolution
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
-- 元の指定模型と有限完備化の自然性の型を照合するために必要。
set_option maxHeartbeats 600000
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 元の指定半自由模型による、完備化前の導来係数拡大の自然同型。 -/
def affineResolvedDerivedScalarIso (P : OrientedPrism p A) :
    DerivedCategory.Q ⋙ complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom ≅
    complexResolutionFunctor A ⋙
      (ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q :=
  NatIso.ofComponents (fun K => by
    let q : (complexResolutionFunctor A).obj K ⟶ K := (complexResolutionAugmentation A).app K
    exact nativeDerivedScalarModelIso (Construction61.crystallineCoverMap P).toRingHom q
      (complexResolutionAugmentation_quasiIso A K) (complexResolutionFunctor_kFlat A K)) (by
    intro K L g
    exact nativeDerivedScalarModelIso_naturality (Construction61.crystallineCoverMap P).toRingHom
      ((complexResolutionAugmentation A).app K) (complexResolutionAugmentation_quasiIso A K)
      (complexResolutionFunctor_kFlat A K)
      ((complexResolutionAugmentation A).app L) (complexResolutionAugmentation_quasiIso A L)
      (complexResolutionFunctor_kFlat A L) g ((complexResolutionFunctor A).map g)
      (by simpa only [Functor.id_map] using ((complexResolutionAugmentation A).naturality g).symm))

/-- 元の完備導来被覆を同じ指定半自由分解で計算する自然同型。 -/
def affineNativeCompletedCoverModelIso (P : OrientedPrism p A) :
    DerivedCategory.Q ⋙ complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom ⋙
      finiteDerivedCompletionFunctor (coverImageCoordinates P) ≅
    complexResolutionFunctor A ⋙ Construction61.completedCoverModelFunctor P ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight (affineResolvedDerivedScalarIso P)
      (finiteDerivedCompletionFunctor (coverImageCoordinates P)) ≪≫
    Functor.isoWhiskerLeft (complexResolutionFunctor A ⋙
      (ModuleCat.extendScalars (Construction61.crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ))
      (finiteDerivedCompletionComparison (coverImageCoordinates P)) ≪≫
    Functor.isoWhiskerLeft (complexResolutionFunctor A) (coverImageCompletionNatIso P)

/-- 元の完備導来関手の射は、元の同じ指定分解の被覆像へ自然に移る。 -/
@[reassoc] theorem affineNativeCompletedCoverModelIso_naturality
    (P : OrientedPrism p A) {K L : Complex A} (g : K ⟶ L) :
    (finiteDerivedCompletionFunctor (coverImageCoordinates P)).map
      ((complexDerivedExtension (Construction61.crystallineCoverMap P).toRingHom).map
        (DerivedCategory.Q.map g)) ≫ (affineNativeCompletedCoverModelIso P).hom.app L =
    (affineNativeCompletedCoverModelIso P).hom.app K ≫
      DerivedCategory.Q.map ((Construction61.completedCoverModelFunctor P).map
        ((complexResolutionFunctor A).map g)) :=
  (affineNativeCompletedCoverModelIso P).hom.naturality g

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
