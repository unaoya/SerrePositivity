module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationPerfectRealization
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationRealizedConeBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYoneda
public import SerrePositivity.KST.SConstruction.DGPerfectStrictNatTransLift

/-!
概要：元実逆回転 cone の右包含を同じ二つの実 Perf 全族の間に保持する。
方針：元代表と同じ strict Perf realization を合成し、元全自然変換を全 Hom ごと制限する。
規約：元対象・元包含・元全自然性を変更しない。
使われ方：元始域の二段 Perf 評価包含と固定 ν 上指定二単体の接続。
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

local notation "GYV" => DGFunctor.comp
  (DGFunctor.comp (G) (dgYoneda R (U))) (V)
local notation "VP" => dgPerfectRealizationPerfect R (U) E (J)

/-- 概要：元右軸の代表評価前の同じ実 Perf 全族。
方針：元代表を同じ実評価で送る。
規約：同じ全対象像・全 Hom を保持。使われ方：元包含の実 Perf 始域。 -/
def dgIdentityInverseRotationPerfectTargetFamily : DGFunctor R (L) (PerfectDGModule R E) :=
  ((G).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (U))).comp (VP)

/-- 概要：元右軸 Perf 全族は包含後に元全評価族そのもの。
方針：元評価の包含則と元 Yoneda の全包含回収を使う。
規約：全 dg 関手の等号。使われ方：元包含の全自然性の制限。 -/
lemma dgIdentityInverseRotationPerfectTargetFamily_underlying :
    dgPerfectModuleUnderlying R E (dgIdentityInverseRotationPerfectTargetFamily R E) = (GYV) := by
  change dgPerfectModuleUnderlying R E
    (((G).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (U))).comp (VP)) = (GYV)
  rw [dgPerfectRealizationPerfect_underlying, dgPerfectModuleUnderlying_inclusion]
  exact congrArg (fun f => f.comp (V))
    ((strictDGFunctor_comp_assoc (G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (U))
      (perfectDGModuleInclusion R (U) Set.univ)).trans
        (congrArg (fun f => (G).comp f) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion R (U))))

/-- 概要：元実逆回転 cone の元右包含を同じ実 Perf 全族間に保持する。
方針：元全 Hom 複体を持つ Perf へ元厳密自然変換を制限する。
規約：同じ元 cycle と全自然性。使われ方：元二段 Perf 包含辺。 -/
def dgIdentityInverseRotationPerfectConeInr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgIdentityInverseRotationPerfectTargetFamily R E)
      (dgIdentityInverseRotationPerfectRealizedConeFamily R E) :=
  dgPerfectStrictNatTransLift R E
    (dgIdentityInverseRotationPerfectTargetFamily R E)
    (dgIdentityInverseRotationPerfectRealizedConeFamily R E)
    (dgIdentityInverseRotationPerfectTargetFamily_underlying R E)
    (dgIdentityInverseRotationPerfectRealizedConeFamily_underlying R E)
    (dgIdentityInverseRotationRealizedConeInr R E)

/-- 概要：元 Perf 包含は全加群への包含後に元全厳密包含を回収する。
方針：同じ元変換の一般の Perf 制限回収を特殊化する。
規約：元 cycle・全自然性を保持。使われ方：元上二単体の包含辺照合。 -/
lemma dgIdentityInverseRotationPerfectConeInr_inclusion :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgIdentityInverseRotationPerfectConeInr R E)
      (perfectDGModuleInclusion R E Set.univ)) (dgIdentityInverseRotationRealizedConeInr R E) :=
  dgPerfectStrictNatTransLift_inclusion R E
    (dgIdentityInverseRotationPerfectTargetFamily R E)
    (dgIdentityInverseRotationPerfectRealizedConeFamily R E)
    (dgIdentityInverseRotationPerfectTargetFamily_underlying R E)
    (dgIdentityInverseRotationPerfectRealizedConeFamily_underlying R E)
    (dgIdentityInverseRotationRealizedConeInr R E)
end SerrePositivity.KST.SConstruction
