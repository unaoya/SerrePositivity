module
public import SerrePositivity.KST.SConstruction.DGBimoduleClosedZero
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor

/-! # 指定閉零対象での双加群の実零値
概要：左右どちらかの指定閉零対象における双加群の値は、全複体として実零となる。
方針：左では元の Yoneda 同型、右では元の加群評価で零性を運ぶ。
規約：元の双加群と対象を保持。使われ方：二軸への射の零比較境界。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

/-- 元の閉零左対象での双加群の値は、同じ実零複体。 -/
lemma dgBimoduleClosedZeroLeft_value (z : C)
    (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (d : D) :
    IsZero (M.value z d) :=
  (dgRepresentableClosedZeroHom R z hz (M.rightAt d)).of_iso
    (dgYonedaIso R z (M.rightAt d)).symm

/-- 元の閉零右対象での双加群の値も、同じ実零複体。 -/
lemma dgBimoduleClosedZeroRight_value (z : D)
    (hz : IsZero (ForgetEnrichment.of (Complex R) z)) (c : C) :
    IsZero (M.value c z) :=
  (moduleEvaluation R C c).map_isZero (dgBimoduleClosedZero_isZero R C D M z hz)

end SerrePositivity.KST.SConstruction
