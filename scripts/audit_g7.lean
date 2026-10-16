import SerrePositivity.HomologicalAlgebra.ExactChainHomologyColimits
import SerrePositivity.HomologicalAlgebra.TorExactColimits
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

-- Exact arbitrary shapes and the original G7-Finset requirement.
assert_no_sorry SerrePositivity.chainDiagramComplex
#print axioms SerrePositivity.chainDiagramComplex
assert_no_sorry SerrePositivity.chainDiagramHomologyIso
#print axioms SerrePositivity.chainDiagramHomologyIso
assert_no_sorry SerrePositivity.chainColimitHomologyIso
#print axioms SerrePositivity.chainColimitHomologyIso
assert_no_sorry SerrePositivity.chainColimitHomologyIso_ι
#print axioms SerrePositivity.chainColimitHomologyIso_ι
assert_no_sorry SerrePositivity.chainHomology_preservesExactColimits
#print axioms SerrePositivity.chainHomology_preservesExactColimits
assert_no_sorry SerrePositivity.moduleTensorChain_preservesColimitsOfShape
#print axioms SerrePositivity.moduleTensorChain_preservesColimitsOfShape
assert_no_sorry SerrePositivity.tor_preservesExactColimits
#print axioms SerrePositivity.tor_preservesExactColimits
assert_no_sorry SerrePositivity.torAlg_preservesExactColimits
#print axioms SerrePositivity.torAlg_preservesExactColimits
assert_no_sorry SerrePositivity.moduleCat_hasExactFinsetColimits
#print axioms SerrePositivity.moduleCat_hasExactFinsetColimits
assert_no_sorry SerrePositivity.torAlg_preservesFinsetColimits
#print axioms SerrePositivity.torAlg_preservesFinsetColimits
assert_no_sorry SerrePositivity.torAlgFinsetColimitIso
#print axioms SerrePositivity.torAlgFinsetColimitIso
assert_no_sorry SerrePositivity.torAlgFinsetColimitIso_ι
#print axioms SerrePositivity.torAlgFinsetColimitIso_ι
assert_no_sorry SerrePositivity.torAlg_finsetColimit_isZero_of_stages
#print axioms SerrePositivity.torAlg_finsetColimit_isZero_of_stages

-- Exact requested signature: no finiteness, countability, or map assumptions.
example {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type u) (n : ℕ) :
    PreservesColimitsOfShape (Finset ι) ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived n) :=
  torAlg_preservesFinsetColimits ι φ n

-- BS's actual indexing shape, with arbitrary root-family type σ.
example {R S σ : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : Finset (σ × ℕ) ⥤ ModuleCat.{u} R) (n : ℕ) :
    PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived n) := by
  let := torAlg_preservesFinsetColimits (σ × ℕ) φ n
  infer_instance

-- The actual comparison preserves every standard stage map.
example {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (ι : Type u)
    (F : Finset ι ⥤ ModuleCat.{u} R) (i : ℕ) (s : Finset ι) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).map (colimit.ι F s) ≫
        (torAlgFinsetColimitIso ι φ F i).hom =
      colimit.ι (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) s :=
  torAlgFinsetColimitIso_ι ι φ F i s

-- Empty root families and degree zero are also covered.
example {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    PreservesColimitsOfShape (Finset (PEmpty : Type u))
      ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived 0) :=
  torAlg_preservesFinsetColimits PEmpty φ 0
