module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSpanUnits
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellComposite
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellDiagonalUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositorPreSpan
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedLeftUnitCoherence
/-!
概要：実 diagonal span の tensor 像から cell 合成の単位比較を構成する。
方針：実 composeMap の準同型性・κ の span 正方形と通常単位三角式を使う。
規約：原 kernel に平坦性を仮定しない。使われ方：coherent cell 合成子の単位。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E] (P : Bimodule R E D)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "M" => dgKernelCellModel R D E P
local notation "m" => BimoduleCategory.underlying R EC DC M
local notation "I0" => dgKernelCellModel R E E (Bimodule.diagonal R E)
local notation "I1" => BimoduleCategory.of R EC EC (Bimodule.diagonal R EC)
local notation "ρ" => dgKernelCellDiagonalResolution R E
local notation "p" => BimoduleSemifreeResolution.π (dgKernelCellDiagonalResolution R E)
local notation "hp" => BimoduleSemifreeResolution.quasiIso
  (dgKernelCellDiagonalResolution R E)
local notation "Φ" => dgKernelDerivedInfinity R DC EC m
local notation "b" => dgKernelCellDiagonalResolutionToCanonical R E
local notation "hP" => dgKernelCellModel_rightRelativeKFlat R D E P
local notation "h0" => dgKernelCellModel_rightRelativeKFlat R E E (Bimodule.diagonal R E)
local notation "h1" => Bimodule.diagonal_rightRelativeKFlat R EC
local notation "h2" => dgKernelCellDiagonalResolution_rightRelativeKFlat R E
local notation "hb" => dgKernelCellDiagonalResolutionToCanonical_quasiIso R E
local notation "a0" => dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC
  (BimoduleTensor.composeMap R EC EC DC b (𝟙 M))
  (BimoduleTensor.composeMap_first_quasiIso R EC EC DC M hP b hb)
local notation "a1" => dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC
  (BimoduleTensor.composeMap R EC EC DC p (𝟙 M))
  (BimoduleTensor.composeMap_first_quasiIso R EC EC DC M hP p hp)
local notation "unitIso" => dgKernelDerivedInfinity_bimoduleIso R DC EC
  (BimoduleTensor.leftBimoduleUnitIso R EC DC m)
def dgKernelCellTargetUnitComparisonIso :
    FunctorIso
      (dgKernelDerivedInfinity R DC EC
        (dgKernelCellComposite R D E E P (Bimodule.diagonal R E)))
      (dgKernelDerivedInfinity R DC EC m) :=
  (a0).symm ≪≫ a1 ≪≫ unitIso
lemma dgKernelCellTargetUnitComparisonIso_value :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC EC
      m (BimoduleCategory.underlying R EC EC I0) hP ≪≫
        dgKernelCellTargetUnitComparisonIso R D E P =
      (dgKernelCellDiagonalUnitIso R E).precomp Φ := by
  have hs := dgKernelDerivedInfinity_compIso_pre_span R DC EC EC M b p
    hP h0 h1 h2 hb hp
  have hu := dgKernelDerivedInfinity_compIso_left_unit R DC EC m hP
  exact functorIso_pre_span_unit Φ
    (dgKernelDerivedInfinity R EC EC (BimoduleCategory.underlying R EC EC I0))
    (dgKernelDerivedInfinity R EC EC (Bimodule.diagonal R EC))
    (dgKernelDerivedInfinity R EC EC (BimoduleCategory.underlying R EC EC (ρ).obj))
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R EC EC b hb)
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R EC EC p hp) a0 a1
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC EC
      m (BimoduleCategory.underlying R EC EC I0) hP)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC EC
      m (Bimodule.diagonal R EC) hP)
    (dgKernelDerivedInfinity_identityIso R EC) unitIso hs hu
end
end SerrePositivity.InfinityCategories
