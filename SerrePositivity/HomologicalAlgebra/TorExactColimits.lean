module

public import SerrePositivity.HomologicalAlgebra.TorSequentialColimits
public import SerrePositivity.HomologicalAlgebra.ExactChainHomologyColimits
public import Mathlib.Data.Finset.Lattice.Basic

/-! # Actual Tor and TorAlg preserve exact colimits, including arbitrary finite-subset diagrams -/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S]
variable {J : Type u} [Category.{v} J]

lemma moduleTensorChain_preservesColimitsOfShape (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    PreservesColimitsOfShape J (moduleTensorChainFunctor K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  exact preservesColimitsOfShape_of_natIso (moduleTensorChainEvalIso K n).symm

variable [HasColimitsOfShape J (ModuleCat.{u} R)]
    [HasExactColimitsOfShape J (ModuleCat.{u} R)]

/-- Ordinary Tor preserves every exact colimit shape, with its original maps. -/
lemma tor_preservesExactColimits (M : ModuleCat.{u} R) (i : ℕ) :
    PreservesColimitsOfShape J ((Tor (ModuleCat.{u} R) i).obj M) := by
  let P := projectiveResolution M
  let hTensor := moduleTensorChain_preservesColimitsOfShape (J := J) P.complex
  let hHomology := chainHomology_preservesExactColimits (J := J) (C := ModuleCat.{u} R) i
  exact preservesColimitsOfShape_of_natIso (torFixedResolutionNatIso M P i).symm

variable [HasColimitsOfShape J (ModuleCat.{u} S)]

/-- The actual scalar-extension left derived functor preserves every exact module colimit shape. -/
lemma torAlg_preservesExactColimits (φ : R →+* S) (i : ℕ) :
    PreservesColimitsOfShape J ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) := by
  let hTor := tor_preservesExactColimits (J := J)
    ((ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of S S)) i
  let hComposite := preservesColimitsOfShape_of_natIso (J := J) (scalarExtensionTorNatIso φ i).symm
  let hRestrict : PreservesColimitsOfShape J (ModuleCat.restrictScalars.{u} φ) :=
    ⟨fun {_} ↦ inferInstance⟩
  let hReflect : ReflectsColimitsOfShape J (ModuleCat.restrictScalars.{u} φ) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) (ModuleCat.restrictScalars.{u} φ)

section Finset
variable (ι : Type u)

/-- Exact filtered colimits at the actual `(0,u)` universe of a finite-subset category. -/
lemma moduleCat_hasExactFinsetColimits : HasExactColimitsOfShape (Finset ι) (ModuleCat.{u} R) := by
  classical
  let hAB : AB5OfSize.{0, u} (ModuleCat.{u} R) :=
    AB5OfSize_of_univLE.{0, u, u, u} _
  infer_instance

/-- G7-Finset: arbitrary finite subsets, all degrees, and arbitrary transition maps. -/
lemma torAlg_preservesFinsetColimits (φ : R →+* S) (i : ℕ) :
    PreservesColimitsOfShape (Finset ι) ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) := by
  let := moduleCat_hasExactFinsetColimits (R := R) ι
  exact torAlg_preservesExactColimits (J := Finset ι) φ i

/-- The requested comparison is exactly the standard colimit-preservation comparison. -/
def torAlgFinsetColimitIso (φ : R →+* S) (F : Finset ι ⥤ ModuleCat.{u} R) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (colimit F) ≅
      colimit (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) := by
  let := torAlg_preservesFinsetColimits ι φ i
  exact preservesColimitIso ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) F

lemma torAlgFinsetColimitIso_ι (φ : R →+* S) (F : Finset ι ⥤ ModuleCat.{u} R)
    (i : ℕ) (s : Finset ι) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).map (colimit.ι F s) ≫
        (torAlgFinsetColimitIso ι φ F i).hom =
      colimit.ι (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) s := by
  let := torAlg_preservesFinsetColimits ι φ i
  exact ι_preservesColimitIso_hom _ _ s

lemma torAlg_finsetColimit_isZero_of_stages (φ : R →+* S)
    (F : Finset ι ⥤ ModuleCat.{u} R) (i : ℕ)
    (h : ∀ s, IsZero (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (F.obj s))) :
    IsZero (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (colimit F)) := by
  apply IsZero.of_iso ?_ (torAlgFinsetColimitIso ι φ F i)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro s
  exact (h s).eq_of_src _ _

end Finset
end SerrePositivity
