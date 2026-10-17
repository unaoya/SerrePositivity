import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe w v uD vD u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

section DerivedCommonBoundary
-- No model structure; the common whole boundary follows from the existing endpoint equations.
variable {D : Type uD} [Category.{vD} D] (K F V : D ⥤ SSet.{w})
  (i : V ⟶ K) (c : V ⟶ F) (a b : NerveBiparameter.System K F)
  (ha : a ≫ NerveBiparameterMaps.restriction V K F i = NerveNaturalBoundary.ofNatTrans V F c)
  (hb : b ≫ NerveBiparameterMaps.restriction V K F i = NerveNaturalBoundary.ofNatTrans V F c)
open NerveCylinderBoundary NerveBiparameterMaps NerveProductParameter NerveMovingIntervalBoundary

example : glue K F a b ≫ restriction _ _ F (vertical zero K) = expand K F point a :=
  glue_zero _ _ _ _

example : glue K F a b ≫ restriction _ _ F (vertical one K) = expand K F point b :=
  glue_one _ _ _ _

example : glue K F a b ≫ restriction _ _ F (horizontal V K i ends) =
    NerveNaturalBoundary.ofNatTrans (product V (SSet.stdSimplex.obj (SimplexCategory.mk 1))) F
      (projection V _ ≫ c) ≫ restriction _ _ F (vertical (SSet.boundary 1).ι V) :=
  common_boundary K F V i c a b ha hb _
end DerivedCommonBoundary

section ActualAllCenterBoundary
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
open ResolutionArrowComparisonEndpoints
open ResolutionArrowCylinderBoundary

example (e : Arrow (ResolutionArrowDiagram.Index C)) : Mono ((inclusion C).app e) :=
  inclusion_mono C e

-- The two actual whole endpoint systems and the entire vertex cylinder are retained.
example : system C hcof ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (zeroInclusion C) =
      NerveProductParameter.expand _ _ _ (left C hcof) := system_zero C hcof

example : system C hcof ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (oneInclusion C) =
      NerveProductParameter.expand _ _ _ (right C hcof) := system_one C hcof

variable (n : ℕ) (old : NerveMovingParameter.LowerSystem.{u, v} (fullParameter C) (values C) n)
  (hboundary : old ≫ Functor.whiskerLeft
      (Reedy.lowerInclusion (NerveCoherentFamily.reedy _) n)
        (NerveMovingParameterRelative.restriction (boundaryParameter C) (fullParameter C)
          (inclusion C) (values C)) =
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy _) n) (system C hcof))

-- A prescribed complete lower system is retained along with the proved whole boundary.
example : Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy _) n)
    (extend C hcof n old hboundary) = old := extend_restrict C hcof n old hboundary

example : extend C hcof n old hboundary ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (zeroInclusion C ≫ inclusion C) =
      NerveProductParameter.expand _ _ _ (left C hcof) := extend_zero C hcof n old hboundary

example : extend C hcof n old hboundary ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (oneInclusion C ≫ inclusion C) =
      NerveProductParameter.expand _ _ _ (right C hcof) := extend_one C hcof n old hboundary

example : extend C hcof n old hboundary ≫ NerveBiparameterMaps.restriction _ _
    (NerveMovingParameter.lifted (values C)) (NerveCylinderBoundary.horizontal
      (vertexParameter C) (parameter C) (vertexInclusion C) interval.{max u v}) = vertices C :=
  extend_vertices C hcof n old hboundary
end ActualAllCenterBoundary

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.BinaryCotensor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveBinaryBoundary,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveProductParameter,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveMovingIntervalBoundary,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowCylinderBoundary]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some actual all-center cylinder boundary modules were not audited"
  logInfo m!"Actual cylinder boundary audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
