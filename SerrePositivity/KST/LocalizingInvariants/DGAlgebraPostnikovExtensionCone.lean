module

public import SerrePositivity.KST.LocalizingInvariants.CochainConeSplitPullback
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovKernel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovShiftedLayer

/-!
概要：Postnikov 隣接拡大の層から、底への全射準同型な cone 複体を構成する。
方針：層の実 kernel 表示と cone 比較を用い、元の遷移と shift 境界を保持する。
規約：cone の乗法と derivation は未構成。使われ方：非分裂拡大の実代数模型の担体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

def postnikovExtensionCone : Complex R := mappingCone (postnikovLayerInclusion R B n)

def postnikovExtensionConeProjection : postnikovExtensionCone R B n ⟶ (postnikov R B n).X :=
  cochainConeQuotient (postnikovLayerInclusion R B n)
    (postnikovTransition R B (n + 1) n (by omega)).hom
    (postnikovLayerInclusion_transition_zero R B n)

lemma postnikovExtensionConeProjection_epi : Epi (postnikovExtensionConeProjection R B n) :=
  cochainConeQuotient_epi _ _ _

lemma postnikovExtensionConeProjection_quasiIso :
    QuasiIso (postnikovExtensionConeProjection R B n) :=
  cochainConeQuotient_quasiIso _ _ _ (postnikovLayerToKernel_quasiIso R B n)

lemma postnikovExtensionCone_inr_projection :
    mappingCone.inr (postnikovLayerInclusion R B n) ≫ postnikovExtensionConeProjection R B n =
      (postnikovTransition R B (n + 1) n (by omega)).hom := cochainConeQuotient_inr _ _ _

def postnikovExtensionConeLinearClass (hn : 0 ≤ n) :
    postnikovExtensionCone R B n ⟶ (postnikovDerivationTarget R B n hn).X :=
  cochainConeToSplit (postnikovLayerInclusion R B n)
    (postnikovTransition R B (n + 1) n (by omega)).hom
    (postnikovLayerInclusion_transition_zero R B n)

lemma postnikovExtensionConeLinearClass_projection (hn : 0 ≤ n) :
    postnikovExtensionConeLinearClass R B n hn ≫
      (SquareZero.projection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)).hom =
        postnikovExtensionConeProjection R B n := cochainConeToSplit_fst _ _ _

lemma postnikovExtensionConeLinearClass_inr (hn : 0 ≤ n) :
    mappingCone.inr (postnikovLayerInclusion R B n) ≫ postnikovExtensionConeLinearClass R B n hn =
      (postnikovTransition R B (n + 1) n (by omega)).hom ≫
        (SquareZero.zeroSection (postnikov R B n)
          (postnikovShiftedLayerBimodule R B n hn 1)).hom := cochainConeToSplit_condition _ _ _

def postnikovExtensionConePullback (hn : 0 ≤ n) :
    PullbackCone (postnikovExtensionConeLinearClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n)
        (postnikovShiftedLayerBimodule R B n hn 1)).hom :=
  PullbackCone.mk (mappingCone.inr (postnikovLayerInclusion R B n))
    (postnikovTransition R B (n + 1) n (by omega)).hom
    (postnikovExtensionConeLinearClass_inr R B n hn)

def postnikovExtensionConePullback_isLimit (hn : 0 ≤ n) :
    IsLimit (postnikovExtensionConePullback R B n hn) :=
  cochainConeSplitPullback_isLimit _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
