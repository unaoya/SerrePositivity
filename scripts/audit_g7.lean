import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
import Mathlib.Util.AssertNoSorry

universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits SerrePositivity

assert_no_sorry SerrePositivity.moduleTensorChainFunctor
#print axioms SerrePositivity.moduleTensorChainFunctor
assert_no_sorry SerrePositivity.moduleTensorChainEvalIso
#print axioms SerrePositivity.moduleTensorChainEvalIso
assert_no_sorry SerrePositivity.moduleTensorChainRealizationIso
#print axioms SerrePositivity.moduleTensorChainRealizationIso
assert_no_sorry SerrePositivity.moduleTensorChainRealizationIso_naturality
#print axioms SerrePositivity.moduleTensorChainRealizationIso_naturality
assert_no_sorry SerrePositivity.moduleTensorChainRealizationNatIso
#print axioms SerrePositivity.moduleTensorChainRealizationNatIso
assert_no_sorry SerrePositivity.torFixedResolutionNatIso
#print axioms SerrePositivity.torFixedResolutionNatIso
assert_no_sorry SerrePositivity.sequentialChainDiagramComplex
#print axioms SerrePositivity.sequentialChainDiagramComplex
assert_no_sorry SerrePositivity.sequentialChainDiagramHomologyIso
#print axioms SerrePositivity.sequentialChainDiagramHomologyIso
assert_no_sorry SerrePositivity.sequentialChainColimitHomologyIso
#print axioms SerrePositivity.sequentialChainColimitHomologyIso
assert_no_sorry SerrePositivity.sequentialChainColimitHomologyIso_ι
#print axioms SerrePositivity.sequentialChainColimitHomologyIso_ι
assert_no_sorry SerrePositivity.chainHomology_preservesSequentialColimits
#print axioms SerrePositivity.chainHomology_preservesSequentialColimits
assert_no_sorry SerrePositivity.moduleCat_hasExactSequentialColimits
#print axioms SerrePositivity.moduleCat_hasExactSequentialColimits
assert_no_sorry SerrePositivity.moduleTensorChain_preservesSequentialColimits
#print axioms SerrePositivity.moduleTensorChain_preservesSequentialColimits
assert_no_sorry SerrePositivity.tor_preservesSequentialColimits
#print axioms SerrePositivity.tor_preservesSequentialColimits
assert_no_sorry SerrePositivity.scalarExtensionTorNatIso
#print axioms SerrePositivity.scalarExtensionTorNatIso
assert_no_sorry SerrePositivity.torAlg_preservesSequentialColimits
#print axioms SerrePositivity.torAlg_preservesSequentialColimits
assert_no_sorry SerrePositivity.torAlgSequentialColimitIso
#print axioms SerrePositivity.torAlgSequentialColimitIso
assert_no_sorry SerrePositivity.torAlgSequentialColimitIso_ι
#print axioms SerrePositivity.torAlgSequentialColimitIso_ι
assert_no_sorry SerrePositivity.torAlg_colimit_isZero_of_stages
#print axioms SerrePositivity.torAlg_colimit_isZero_of_stages

-- Exact original G7 signature; arbitrary diagram maps, all degrees, arbitrary same universe.
example {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
    (F : ℕ ⥤ ModuleCat.{u} R) (i : ℕ) :
    PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) := by
  let h := torAlg_preservesSequentialColimits φ i
  infer_instance

-- The requested orientation is the original standard comparison.
example {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
    (F : ℕ ⥤ ModuleCat.{u} R) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (colimit F) ≅
      colimit (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) :=
  torAlgSequentialColimitIso φ F i

-- Every original stage inclusion is preserved, also in degree zero.
example {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
    (F : ℕ ⥤ ModuleCat.{u} R) (i n : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).map (colimit.ι F n) ≫
        (torAlgSequentialColimitIso φ F i).hom =
      colimit.ι (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) n :=
  torAlgSequentialColimitIso_ι φ F i n

-- Stagewise vanishing passes to the colimit without flatness or injectivity assumptions.
example {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
    (F : ℕ ⥤ ModuleCat.{u} R) (i : ℕ)
    (h : ∀ n, IsZero (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (F.obj n))) :
    IsZero (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (colimit F)) :=
  torAlg_colimit_isZero_of_stages φ F i h
