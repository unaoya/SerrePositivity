module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelQuasiIsoCompositorNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.IsoSpanSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoSandwichCoherentUnits
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
  (P : BimoduleCategory R E D) {Q0 Q1 Q2 : BimoduleCategory R F E}
  (g0 : Q2 ⟶ Q0) (g1 : Q2 ⟶ Q1)
  (hP : Bimodule.rightRelativeKFlat R E D (BimoduleCategory.underlying R E D P))
  (hQ0 : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q0))
  (hQ1 : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q1))
  (hQ2 : Bimodule.rightRelativeKFlat R F E (BimoduleCategory.underlying R F E Q2))
  (hg0 : BimoduleCategory.quasiIso R F E g0) (hg1 : BimoduleCategory.quasiIso R F E g1)
local notation "Φ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P)
local notation "Ψ0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F (BimoduleCategory.underlying R F E Q0)
local notation "Ψ1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F (BimoduleCategory.underlying R F E Q1)
local notation "Ψ2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E F (BimoduleCategory.underlying R F E Q2)
local notation "κ0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
  (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R F E Q0) hP
local notation "κ1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
  (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R F E Q1) hP
local notation "κ2" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R D E F
  (BimoduleCategory.underlying R E D P) (BimoduleCategory.underlying R F E Q2) hP
local notation "a0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R E F g0 hg0
local notation "a1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R E F g1 hg1
local notation "b0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D F
  (BimoduleTensor.composeMap R F E D g0 (𝟙 P))
  (BimoduleTensor.composeMap_first_quasiIso R F E D P hP g0 hg0)
local notation "b1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D F
  (BimoduleTensor.composeMap R F E D g1 (𝟙 P))
  (BimoduleTensor.composeMap_first_quasiIso R F E D P hP g1 hg1)
include hQ0 hQ1 hQ2 in
lemma dgKernelDerivedInfinity_compIso_pre_span :
    κ0 ≪≫ (b0).symm ≪≫ b1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (a0).symm Φ ≪≫ (a1).precomp Φ ≪≫ κ1 := by
  have h0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_quasiIso_naturality R D E F
    (𝟙 P) g0 hP hP hQ2 hQ0 ((BimoduleCategory.quasiIso R E D).id_mem P) hg0
  have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_quasiIso_naturality R D E F
    (𝟙 P) g1 hP hP hQ2 hQ1 ((BimoduleCategory.quasiIso R E D).id_mem P) hg1
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_id] at h0 h1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_refl Φ Ψ2] at h0 h1
  simp only [Iso.refl_trans] at h0 h1
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_span_square ((a0).precomp Φ) ((a1).precomp Φ) b0 b1 κ0 κ1 κ2 h0 h1
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
