module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGKernelQuasiIsoCompositorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.IsoSpanSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.FunctorIsoSandwichCoherentUnits
/-!
概要：実 tensor span の導来像を指定 κ と前後合成の span へ同定する。
方針：元の準同型自然性の二正方形と共通始点の相殺を使う。
規約：射は実 tensor 射である。使われ方：cell の実単位三角式。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E F : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R F] [Small.{u} F]
  {P0 P1 P2 : BimoduleCategory R E D} (Q : BimoduleCategory R F E)
  (f0 : P2 ⟶ P0) (f1 : P2 ⟶ P1)
  (hP0 : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P0))
  (hP1 : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P1))
  (hP2 : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P2))
  (hQ : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q))
  (hf0 : BimoduleCategory.quasiIso R E D f0) (hf1 : BimoduleCategory.quasiIso R E D f1)
local notation "Φ0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P0)
local notation "Φ1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P1)
local notation "Φ2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P2)
local notation "Ψ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F (BimoduleCategory.underlying R F E Q)
local notation "κ0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
  (BimoduleCategory.underlying R E D P0) (BimoduleCategory.underlying R F E Q) hP0
local notation "κ1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
  (BimoduleCategory.underlying R E D P1) (BimoduleCategory.underlying R F E Q) hP1
local notation "κ2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
  (BimoduleCategory.underlying R E D P2) (BimoduleCategory.underlying R F E Q) hP2
local notation "a0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f0 hf0
local notation "a1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D E f1 hf1
local notation "b0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D F
  (BimoduleTensor.composeMap R F E D (𝟙 Q) f0)
  (BimoduleTensor.composeMap_second_kFlat_quasiIso R F E D Q hP2 hP0 f0 hf0)
local notation "b1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D F
  (BimoduleTensor.composeMap R F E D (𝟙 Q) f1)
  (BimoduleTensor.composeMap_second_kFlat_quasiIso R F E D Q hP2 hP1 f1 hf1)
include hQ in
lemma dgKernelDerivedInfinity_compIso_post_span :
    κ0 ≪≫ (b0).symm ≪≫ b1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (a0).symm Ψ ≪≫ (a1).postcomp Ψ ≪≫ κ1 := by
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_quasiIso_naturality R D E F
    f0 (𝟙 Q) hP2 hP0 hQ hQ hf0 ((BimoduleCategory.quasiIso R F E).id_mem Q)
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_quasiIso_naturality R D E F
    f1 (𝟙 Q) hP2 hP1 hQ hQ hf1 ((BimoduleCategory.quasiIso R F E).id_mem Q)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_id] at h0 h1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_refl Ψ Φ0] at h0
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_refl Ψ Φ1] at h1
  simp only [Iso.refl_trans] at h0 h1
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_span_square ((a0).postcomp Ψ) ((a1).postcomp Ψ) b0 b1 κ0 κ1 κ2 h0 h1
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
