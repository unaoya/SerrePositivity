import SerrePositivity.KST.SConstruction.OdotTailAll
import Lean

/-! K-S2 の公開型・公理・主経路の instance 仮定を監査する。 -/

#check @SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLaxEquivalence
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLaxEquivalence
#check @SerrePositivity.KST.SConstruction.dgOdotTailGluingNativeValueEquivalence
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailGluingNativeValueEquivalence
#check @SerrePositivity.KST.SConstruction.dgOdotTailPerfectGluingLaxEquivalence
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailPerfectGluingLaxEquivalence
#check @SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLax_fst
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLax_fst
#check @SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLax_snd
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLax_snd
#check @SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLax_cone
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailNativePerfLax_cone
#check @SerrePositivity.KST.SConstruction.dgOdotTailResolvedProjectionComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailResolvedProjectionComparison
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLowerTriangleComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLowerTriangleComparison
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelSpecifiedLowerComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelSpecifiedLowerComparison
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelSpecifiedLowerComparison_recovery
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelSpecifiedLowerComparison_recovery
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelAbsoluteLowerTriangleComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelAbsoluteLowerTriangleComparison
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelAbsoluteLowerTriangle_whole
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelAbsoluteLowerTriangle_whole
#check @SerrePositivity.KST.SConstruction.dgOdotTailActualKernelLowerTriangleComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailActualKernelLowerTriangleComparison
#check @SerrePositivity.KST.SConstruction.dgOdotTailActualKernelAbsoluteLowerTriangleComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailActualKernelAbsoluteLowerTriangleComparison
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLowerTriangle_inclusion
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLowerTriangle_inclusion
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLowerTriangle_quotient
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLowerTriangle_quotient
#check @SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection
#print axioms SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection
#check @SerrePositivity.KST.SConstruction.dgOdotTailCatPerfConnection
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailCatPerfConnection
#check @SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.isFiber
#print axioms SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.isFiber
#check @SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.actual_isPullback
#print axioms SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.actual_isPullback
#check @SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.completed_isPullback
#print axioms SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.completed_isPullback
#check @SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.sourceValueIso
#print axioms SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.sourceValueIso

#check @SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isIdempotentCompletion
#print axioms SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isIdempotentCompletion

#check @SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.landTammeCone_isLimit
#print axioms SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection.landTammeCone_isLimit
#check @SerrePositivity.KST.SConstruction.dgOdotMilnorNativeSequence
#print axioms SerrePositivity.KST.SConstruction.dgOdotMilnorNativeSequence
#check @SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isResolvedVerdierSequence_of_milnor
#print axioms SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isResolvedVerdierSequence_of_milnor
#check @SerrePositivity.KST.SConstruction.dgOdotMilnorSuppliedOriginalLaxComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotMilnorSuppliedOriginalLaxComparison
#check @SerrePositivity.KST.SConstruction.dgOdotMilnorSuppliedIdentityLaxComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotMilnorSuppliedIdentityLaxComparison
#check @SerrePositivity.KST.SConstruction.dgOdotMilnorSuppliedOriginalLaxConeComparison
#print axioms SerrePositivity.KST.SConstruction.dgOdotMilnorSuppliedOriginalLaxConeComparison

#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftComposite
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftComposite
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftCompStruct
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftCompStruct
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTriangle
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTriangle
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTriangle_edges
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTriangle_edges
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftPerfectTriangle
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftPerfectTriangle
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftPerfectTriangle_inclusion
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftPerfectTriangle_inclusion
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTriangle_nu_edges
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTriangle_nu_edges

#check @SerrePositivity.KST.SConstruction.dgOdotTailCatPerfConnectionOfCertificates
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailCatPerfConnectionOfCertificates

#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftDiagonalTransport
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftDiagonalTransport
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTransportedCompStruct
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftTransportedCompStruct
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftDiagonalTransport_faces
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelLiftDiagonalTransport_faces

#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_upper
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_upper
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_lower
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_lower
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_lower_edges
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_lower_edges
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_upper_edges
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_upper_edges
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_kernel_vertex
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_kernel_vertex
#check @SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_perfect_lower
#print axioms SerrePositivity.KST.SConstruction.dgOdotTailKernelComparisonSquare_perfect_lower

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.KST.SConstruction.DGOdotTailLaxComparison,
    `SerrePositivity.KST.SConstruction.DGOdotTailKernelLowerTriangle,
    `SerrePositivity.KST.SConstruction.DGOdotTailCatPerfConnection,
    `SerrePositivity.KST.SConstruction.DGOdotTailKernelLiftTriangle,
    `SerrePositivity.KST.SConstruction.DGOdotTailKernelComparisonSquare]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    if info.type.getUsedConstants.contains `HomotopicalAlgebra.ModelCategory then
      throwError "K-S2: ModelCategory assumption in {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "K-S2: unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "K-S2: module not audited: {mod}"
  logInfo m!"K-S2 audit passed: {count} declarations in {seen.size} modules."
