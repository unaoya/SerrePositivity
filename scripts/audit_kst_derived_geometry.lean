import SerrePositivity.KST.DerivedGeometry
import Lean.Util.CollectAxioms

/-!
概要：K-L4 の全公開宣言の推移的な公理依存を監査する。
方針：名前空間内の宣言を列挙し collectAxioms で検証する。
規約：propext・Classical.choice・Quot.sound のみを許す。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1、Neeman 1992 Thm 2.1、
TT 3.19・8.1、Toën §3.2 の保存単位ごとの受入検証。
-/

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let required : Array Name := #[
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.forget,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.underlyingCohomology,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.hasQuasicoherentCohomology,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.dqcInclusion,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.forget_reflectsIsomorphisms,
    `SerrePositivity.KST.DerivedGeometry.FiniteAffineCoverOf,
    `SerrePositivity.KST.DerivedGeometry.affineIntersectionCover,
    `SerrePositivity.KST.DerivedGeometry.toSheaf_preservesColimits,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.forget_preservesFiniteLimits,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.forget_preservesColimits,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.forget_preservesFiniteColimits,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.derivedForgetHomologyIso,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.derivedForget_reflectsIsomorphisms,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.dqcForget_reflectsIsomorphisms,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.freeForgetAdjunction,
    `SerrePositivity.KST.DerivedGeometry.globalBaseMap,
    `SerrePositivity.KST.DerivedGeometry.restriction_comp_sectionBaseMap,
    `SerrePositivity.KST.DerivedGeometry.coefficientTensorPresheaf,
    `SerrePositivity.KST.DerivedGeometry.tensorCoefficientSheaf,
    `SerrePositivity.KST.DerivedGeometry.coefficientSheafOfMorphism,
    `SerrePositivity.KST.DerivedGeometry.tensorCoefficientConstant_comp_algebraMap,
    `SerrePositivity.KST.DerivedGeometry.tensorCoefficientSheaf_structureMap_commutes,
    `SerrePositivity.KST.DerivedGeometry.tensorCoefficientSectionAlgebra,
    `SerrePositivity.KST.DerivedGeometry.tensorCoefficientSelfIso,
    `SerrePositivity.KST.DerivedGeometry.sectionAlgebra_spec,
    `SerrePositivity.KST.DerivedGeometry.affineBasicTensorSectionsEquiv,
    `SerrePositivity.KST.DerivedGeometry.affineBasicTensorSectionsEquiv_tmul,
    `SerrePositivity.KST.DerivedGeometry.affineTensorSectionMap_naturality,
    `SerrePositivity.KST.DerivedGeometry.affineTensorToTilde_basic_isIso,
    `SerrePositivity.KST.DerivedGeometry.locallyInjective_of_basis,
    `SerrePositivity.KST.DerivedGeometry.locallySurjective_of_basis,
    `SerrePositivity.KST.DerivedGeometry.affineTensorSheafIso,
    `SerrePositivity.KST.DerivedGeometry.toSheafify_affineTensorSheafIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientAdditiveIso,
    `SerrePositivity.KST.DerivedGeometry.preservesSheafification_of_forget,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientSheafAdditiveIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientSheafAdditiveIso_fac,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientComparison_basic_isIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientComparison_top_isIso,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.regular,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientConstantLinear,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientModuleMap,
    `SerrePositivity.KST.DerivedGeometry.toOpen_affineCoefficientModuleMap,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientModuleMap_tmul,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientModuleMap_fac,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientModuleMap_isIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientModuleIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientRegular_isQuasicoherent,
    `SerrePositivity.KST.DerivedGeometry.tensorBaseChangeCancel,
    `SerrePositivity.KST.DerivedGeometry.tensorBaseChangeRight,
    `SerrePositivity.KST.DerivedGeometry.tensorBaseChangeRight_naturality,
    `SerrePositivity.KST.DerivedGeometry.globalBaseMap_spec,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientBaseChangeIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientBaseChangeIso_unit,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientBaseChangeSheafIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientBaseChangeSheafIso_structureMap,
    `SerrePositivity.KST.DerivedGeometry.affineBaseCoefficientComparison_basic_isIso,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.regularMap,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.regularMap_isIso,
    `SerrePositivity.KST.DerivedGeometry.affineBaseCoefficientModuleIso,
    `SerrePositivity.KST.DerivedGeometry.affineBaseCoefficientRegular_isQuasicoherent,
    `SerrePositivity.KST.DerivedGeometry.coefficientSheafOfSpecMap_regular_isQuasicoherent,
    `SerrePositivity.KST.DerivedGeometry.openEmbedding_isCocontinuous,
    `SerrePositivity.KST.DerivedGeometry.openSheafificationIso,
    `SerrePositivity.KST.DerivedGeometry.openSheafificationIso_fac,
    `SerrePositivity.KST.DerivedGeometry.globalBaseMap_restrict,
    `SerrePositivity.KST.DerivedGeometry.sectionAlgebra_restrict,
    `SerrePositivity.KST.DerivedGeometry.tensorRingPure_cast,
    `SerrePositivity.KST.DerivedGeometry.openTensorPresheafIso,
    `SerrePositivity.KST.DerivedGeometry.openTensorPresheafIso_unit,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.restrict,
    `SerrePositivity.KST.DerivedGeometry.openTensorSheafIso,
    `SerrePositivity.KST.DerivedGeometry.openTensorSheafIso_structureMap,
    `SerrePositivity.KST.DerivedGeometry.coefficientSheafOfMorphism_restrictIso,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.regularRestrictIso,
    `SerrePositivity.KST.DerivedGeometry.openTensorRegularIso,
    `SerrePositivity.KST.DerivedGeometry.coefficientSheafOfMorphism_regularRestrictIso,
    `SerrePositivity.KST.DerivedGeometry.openImmersionStructureMap,
    `SerrePositivity.KST.DerivedGeometry.appIso_inv_comp_sectionBaseMap,
    `SerrePositivity.KST.DerivedGeometry.openImmersionSectionAlgEquiv,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.restrictAlong,
    `SerrePositivity.KST.DerivedGeometry.openImmersionTensorPresheafIso,
    `SerrePositivity.KST.DerivedGeometry.openImmersionTensorSheafIso,
    `SerrePositivity.KST.DerivedGeometry.openImmersionTensorSheafIso_structureMap,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.regularRestrictAlongIso,
    `SerrePositivity.KST.DerivedGeometry.openImmersionTensorRegularIso,
    `SerrePositivity.KST.DerivedGeometry.affineSchemeCoefficientRegular_isQuasicoherent,
    `SerrePositivity.KST.DerivedGeometry.moduleOver_isQuasicoherent_of_restrict,
    `SerrePositivity.KST.DerivedGeometry.module_isQuasicoherent_of_openCover,
    `SerrePositivity.KST.DerivedGeometry.tensorCoefficientRegular_isQuasicoherent,
    `SerrePositivity.KST.DerivedGeometry.coefficientSheafOfMorphism_regular_isQuasicoherent,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.hasQuasicoherentUnderlying,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.qcohForget,
    `SerrePositivity.KST.DerivedGeometry.CoefficientSheaf.qcohForget_reflectsIsomorphisms,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientGlobalIso,
    `SerrePositivity.KST.DerivedGeometry.affineCoefficientΓ,
    `SerrePositivity.KST.DerivedGeometry.affineQcohΓForgetIso,
    `SerrePositivity.KST.DerivedGeometry.affineQcohΓ_faithful,
    `SerrePositivity.KST.DerivedGeometry.affineQcohΓ_reflectsIsomorphisms,
    `SerrePositivity.KST.DerivedGeometry.affineUnderlyingHom_ext,
    `SerrePositivity.KST.DerivedGeometry.coefficientConstantActionRingHom,
    `SerrePositivity.KST.DerivedGeometry.coefficientConstantActionNat,
    `SerrePositivity.KST.DerivedGeometry.affineUnderlyingHom_commutesConstant]
  for name in required do
    unless env.contains name do throwError "Missing K-L4 declaration: {name}"
  for mod in env.header.modules do
    if (`SerrePositivity.KTheory).isPrefixOf mod.module then
      throwError "K-L4 must not depend on K-theory: {mod.module}"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    unless (`SerrePositivity.KST.DerivedGeometry).isPrefixOf name do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax =>
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
    count := count + 1
  if count == 0 then throwError "No K-L4 declarations audited"
  logInfo m!"K-L4 audit: {count} declarations; standard axioms only; no KTheory imports."
