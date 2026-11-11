module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationRealization
public import SerrePositivity.KST.SConstruction.DGPerfectRealizationPerfect

/-!
概要：元恒等 gluing の実逆回転 cone 全族を同じ実像の strict Perf 関手へ持ち上げる。
方針：元実 cone 関手に D 供給で構成した同じ実評価の Perf 制限を後合成する。
規約：元実 cone・元包含・全 Hom を保持し、小さい代表へ置換しない。
使われ方：元二段 realization 全比較を固定 ν 値へ接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type (max (u + 1) v))
  [DGCategory R E] [Small.{u} E]
local notation "I" => DGFunctor.id E
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R E E (dgHomGluingBimodule R E E E (I) (I))
local notation "U" => DGHomGluingLoopConeBase R E E E (I) (I)
local notation "IU" => DGFunctor.id (U)
local notation "family" => dgHomGluingLoopConeFamily R E E E (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R E ((L) ⊕ (L)) (family)
local notation "V" => dgPerfectRealization R (U) E (J)
local notation "F" => dgHomGluingLoopConeSmall R E E E (I) (I)
local notation "G" => dgHomGluingLoopConeShiftedTarget R E E E (I) (I)
local notation "a" => dgHomGluingInverseRotationMap R E E E (I) (I)
local notation "h" => dgHomGluingInverseRotationMap_hom_naturality R E E E (I) (I)
local notation "K" => dgPerfectModuleUnderlying R E (J)
local notation "F0" => DGFunctor.comp (F) (K)
local notation "G0" => DGFunctor.comp (G) (K)

local notation "A" => DGFunctor.comp (dgHomGluingInverseRotationFunctor R E E E (I) (I))
  (dgHomGluingConeFunctor R (U) (U) (U) (IU) (IU))

/-- 概要：同じ元実逆回転 cone の全 realization を strict Perf 値で保持する。
方針：元実評価の証明済み Perf 制限を後合成する。
規約：元対象・元全 Hom を保持。使われ方：固定 ν への元第一段評価。 -/
def dgIdentityInverseRotationPerfectRealizedConeFamily :
    DGFunctor R (L) (PerfectDGModule R E) :=
  (A).comp (dgPerfectRealizationPerfect R (U) E (J))

/-- 概要：元第一段 Perf 全族の全加群像は元の実 realization 全族そのもの。
方針：元の包含回収を同じ実 cone 入力へ適用する。
規約：全関手の等号。使われ方：元指定上二単体・全比較の端点回収。 -/
lemma dgIdentityInverseRotationPerfectRealizedConeFamily_underlying :
    dgPerfectModuleUnderlying R E (dgIdentityInverseRotationPerfectRealizedConeFamily R E) =
      dgIdentityInverseRotationRealizedConeFamily R E :=
  dgPerfectRealizationPerfect_underlying R (U) E (J) (A)
end SerrePositivity.KST.SConstruction
