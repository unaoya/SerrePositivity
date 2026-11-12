module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSpanUnits
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellComposite
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellDiagonalUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCompositorPostSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedRightUnitCoherence
/-!
概要：実 diagonal span の tensor 像から cell 合成の単位比較を構成する。
方針：実 composeMap の準同型性・κ の span 正方形と通常単位三角式を使う。
規約：原 kernel に平坦性を仮定しない。使われ方：coherent cell 合成子の単位。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E] (P : Bimodule R E D)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "M" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P
local notation "m" => BimoduleCategory.underlying R EC DC M
local notation "I0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D D (Bimodule.diagonal R D)
local notation "I1" => BimoduleCategory.of R DC DC (Bimodule.diagonal R DC)
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolution R D
local notation "p" => BimoduleSemifreeResolution.π (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolution R D)
local notation "hp" => BimoduleSemifreeResolution.quasiIso
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolution R D)
local notation "Φ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC m
local notation "b" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical R D
local notation "h0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D D (Bimodule.diagonal R D)
local notation "h1" => Bimodule.diagonal_rightRelativeKFlat R DC
local notation "h2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolution_rightRelativeKFlat R D
local notation "hb" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalResolutionToCanonical_quasiIso R D
local notation "a0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC
  (BimoduleTensor.composeMap R EC DC DC (𝟙 M) b)
  (BimoduleTensor.composeMap_second_kFlat_quasiIso R EC DC DC M h2 h0 b hb)
local notation "a1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC
  (BimoduleTensor.composeMap R EC DC DC (𝟙 M) p)
  (BimoduleTensor.composeMap_second_kFlat_quasiIso R EC DC DC M h2 h1 p hp)
local notation "unitIso" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_bimoduleIso R DC EC
  (BimoduleTensor.rightBimoduleUnitIso R EC DC m)
def dgKernelCellSourceUnitComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D D E (Bimodule.diagonal R D) P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC m) :=
  (a0).symm ≪≫ a1 ≪≫ unitIso
lemma dgKernelCellSourceUnitComparisonIso_value :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC
      (BimoduleCategory.underlying R DC DC I0) m h0 ≪≫
        dgKernelCellSourceUnitComparisonIso R D E P =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalUnitIso R D).postcomp Φ := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_post_span R DC DC EC M b p
    h0 h1 h2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P) hb hp
  have hu := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_right_unit R DC EC m
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_post_span_unit
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC I0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (BimoduleCategory.underlying R DC DC (ρ).obj)) Φ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC DC p hp) a0 a1
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC
      (BimoduleCategory.underlying R DC DC I0) m h0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC DC EC
      (Bimodule.diagonal R DC) m h1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R DC) unitIso hs hu
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
