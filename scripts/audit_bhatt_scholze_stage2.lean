import SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDP
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBaseChange
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBasis
import SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPFactorial
import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
import SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps
import SerrePositivity.BhattScholze.Prismatic.AffinePolynomial
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaBounds
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaFlat
import SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaResidue
import SerrePositivity.BhattScholze.Prismatic.Envelope
import SerrePositivity.BhattScholze.Prismatic.PrismOver
import SerrePositivity.BhattScholze.Prismatic.VariableEnvelope
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedCoefficient
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz
import SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge
import SerrePositivity.CommutativeAlgebra.DeRham.Graded
import SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion
import SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz
import SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass
import SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinCochains
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy
import SerrePositivity.HomologicalAlgebra.Cosimplicial.PrincipalShortExact
import SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient
import SerrePositivity.HomologicalAlgebra.Cosimplicial.ShortExact
import SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve
import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
import SerrePositivity.BhattScholze.Perfectoidization.Derived.FiniteEtalePerfectoid
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality
import SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite
import SerrePositivity.BhattScholze.Prismatic.PolynomialFrobeniusCech
import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity
import SerrePositivity.HomologicalAlgebra.Cech.Basic
import SerrePositivity.HomologicalAlgebra.Cech.BaseChange
import SerrePositivity.HomologicalAlgebra.Cech.Split
import SerrePositivity.HomologicalAlgebra.Cech.Filtered
import SerrePositivity.HomologicalAlgebra.Cech.Diagonal
import SerrePositivity.HomologicalAlgebra.Cech.Double
import SerrePositivity.HomologicalAlgebra.Cech.Composition
import Lean.Util.CollectAxioms

/-!
概要：段階 II で BS の drafts から本体へ移したモジュールを公理監査する。
方針：下の一覧のモジュールで定義された宣言（生成宣言を含む）について、公理の依存を再帰的に調べる。
規約：標準三公理 propext・Classical.choice・Quot.sound だけを許す。新しいモジュールを取り込むたびに、import と一覧の両方に足す。
使われ方：調整役が取り込みのたびに `lake env lean` で実行する（import するモジュールを先に `lake build`）。
-/

open Lean in
run_cmd do
  let mods : Array Name := #[
    `SerrePositivity.HomologicalAlgebra.Cech.Basic,
    `SerrePositivity.HomologicalAlgebra.Cech.BaseChange,
    `SerrePositivity.HomologicalAlgebra.Cech.Split,
    `SerrePositivity.HomologicalAlgebra.Cech.Filtered,
    `SerrePositivity.HomologicalAlgebra.Cech.Diagonal,
    `SerrePositivity.HomologicalAlgebra.Cech.Double,
    `SerrePositivity.HomologicalAlgebra.Cech.Composition,
    `SerrePositivity.BhattScholze.Prismatic.PolynomialFrobeniusCech,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCommutativity,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.FiniteEtalePerfectoid,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt,
    `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDP,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBaseChange,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPBasis,
    `SerrePositivity.BhattScholze.Delta.DividedPower.FreeDPFactorial,
    `SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction,
    `SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeMaps,
    `SerrePositivity.BhattScholze.Prismatic.AffinePolynomial,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDelta,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaBounds,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaFlat,
    `SerrePositivity.BhattScholze.Prismatic.CompletedFreeDeltaResidue,
    `SerrePositivity.BhattScholze.Prismatic.Envelope,
    `SerrePositivity.BhattScholze.Prismatic.PrismOver,
    `SerrePositivity.BhattScholze.Prismatic.VariableEnvelope,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedCoefficient,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedDifferential,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedLeibniz,
    `SerrePositivity.CommutativeAlgebra.DeRham.CompletedWedge,
    `SerrePositivity.CommutativeAlgebra.DeRham.Graded,
    `SerrePositivity.CommutativeAlgebra.DeRham.Polynomial,
    `SerrePositivity.CommutativeAlgebra.DeRham.PolynomialCompletion,
    `SerrePositivity.CommutativeAlgebra.DeRham.PolynomialLeibniz,
    `SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinClass,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.BocksteinCochains,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.CupProduct,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Homotopy,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.PrincipalShortExact,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.ShortExact,
    `SerrePositivity.HomologicalAlgebra.Cosimplicial.SplitCechConerve,
    `SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless mods.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "BS stage II: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "BS stage II: no declarations audited"
  logInfo m!"BS stage II audit passed: {count} declarations, standard three axioms only."
