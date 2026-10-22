module
public import SerrePositivity.KST.SConstruction.DGClosedZeroHom
public import SerrePositivity.DifferentialGraded.Bimodule.Basic

/-! # 双加群の閉零右対象における全 Hom の零性
概要：元の右圏の閉零対象を固定すると、双加群の値への全加群 Hom は実零となる。
方針：双加群の加法的な閉零関手で零性を移し、元の全 Hom 零性を適用する。
規約：ホモトピー零と厳密な閉零を区別する。使われ方：K の実左軸包含。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (z : D) (hz : IsZero (ForgetEnrichment.of (Complex R) z))

include hz in
/-- 元の閉零右対象の像は、同じ右加群の閉零圏で実零対象。 -/
lemma dgBimoduleClosedZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R) (M.rightAt z)) :=
  M.toFunctor.onClosed.map_isZero hz

include hz in
/-- 元の閉零右対象の像への全加群 Hom は、元の全次数を保った実零複体。 -/
lemma dgBimoduleClosedZero_hom (N : RightModule R C) :
    IsZero (homObject R (RightModule R C) N (M.rightAt z)) :=
  dgHom_isZero_of_closed_zero_target R (M.rightAt z)
    (dgBimoduleClosedZero_isZero R C D M z hz) N

end SerrePositivity.KST.SConstruction
