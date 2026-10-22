module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSpanUnits
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellComposite
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellDiagonalUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelCompositorPostSpan
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedRightUnitCoherence
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
local notation "I0" => dgKernelCellModel R D D (Bimodule.diagonal R D)
local notation "I1" => BimoduleCategory.of R DC DC (Bimodule.diagonal R DC)
local notation "ρ" => dgKernelCellDiagonalResolution R D
local notation "p" => BimoduleSemifreeResolution.π (dgKernelCellDiagonalResolution R D)
local notation "hp" => BimoduleSemifreeResolution.quasiIso
  (dgKernelCellDiagonalResolution R D)
local notation "Φ" => dgKernelDerivedInfinity R DC EC m
local notation "b" => dgKernelCellDiagonalResolutionToCanonical R D
local notation "h0" => dgKernelCellModel_rightRelativeKFlat R D D (Bimodule.diagonal R D)
local notation "h1" => Bimodule.diagonal_rightRelativeKFlat R DC
local notation "h2" => dgKernelCellDiagonalResolution_rightRelativeKFlat R D
local notation "hb" => dgKernelCellDiagonalResolutionToCanonical_quasiIso R D
local notation "a0" => dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC
  (BimoduleTensor.composeMap R EC DC DC (𝟙 M) b)
  (BimoduleTensor.composeMap_second_kFlat_quasiIso R EC DC DC M h2 h0 b hb)
local notation "a1" => dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC
  (BimoduleTensor.composeMap R EC DC DC (𝟙 M) p)
  (BimoduleTensor.composeMap_second_kFlat_quasiIso R EC DC DC M h2 h1 p hp)
local notation "unitIso" => dgKernelDerivedInfinity_bimoduleIso R DC EC
  (BimoduleTensor.rightBimoduleUnitIso R EC DC m)
def dgKernelCellSourceUnitComparisonIso :
    FunctorIso
      (dgKernelDerivedInfinity R DC EC
        (dgKernelCellComposite R D D E (Bimodule.diagonal R D) P))
      (dgKernelDerivedInfinity R DC EC m) :=
  (a0).symm ≪≫ a1 ≪≫ unitIso
lemma dgKernelCellSourceUnitComparisonIso_value :
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC
      (BimoduleCategory.underlying R DC DC I0) m h0 ≪≫
        dgKernelCellSourceUnitComparisonIso R D E P =
      (dgKernelCellDiagonalUnitIso R D).postcomp Φ := by
  have hs := dgKernelDerivedInfinity_compIso_post_span R DC DC EC M b p
    h0 h1 h2 (dgKernelCellModel_rightRelativeKFlat R D E P) hb hp
  have hu := dgKernelDerivedInfinity_compIso_right_unit R DC EC m
    (dgKernelCellModel_rightRelativeKFlat R D E P)
  exact functorIso_post_span_unit
    (dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC I0))
    (dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC))
    (dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC (ρ).obj)) Φ
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC b hb)
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC p hp) a0 a1
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC
      (BimoduleCategory.underlying R DC DC I0) m h0)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC
      (Bimodule.diagonal R DC) m h1)
    (dgKernelDerivedInfinity_identityIso R DC) unitIso hs hu
end
end SerrePositivity.InfinityCategories
