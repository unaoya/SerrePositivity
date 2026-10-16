module
public import SerrePositivity.HomologicalAlgebra.BalancedTorResolution
public import SerrePositivity.HomologicalAlgebra.SequentialChainHomologyColimits
public import SerrePositivity.HomologicalAlgebra.DerivedTensorBaseChange
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Existing Tor and TorAlg preserve arbitrary sequential colimits of modules -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The sequential exact-colimit instance at the small indexing universe. -/
lemma moduleCat_hasExactSequentialColimits : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := by
  let hAB : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
    AB5OfSize_of_univLE.{0, 0, u, u} _
  infer_instance

/-- Tensor with any fixed complex preserves sequential colimits term by term. -/
lemma moduleTensorChain_preservesSequentialColimits (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    PreservesColimitsOfShape ℕ (moduleTensorChainFunctor K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  exact preservesColimitsOfShape_of_natIso (moduleTensorChainEvalIso K n).symm

/-- Ordinary Tor commutes with every sequential module colimit, without assumptions on its maps. -/
lemma tor_preservesSequentialColimits (M : ModuleCat.{u} R) (i : ℕ) :
    PreservesColimitsOfShape ℕ ((Tor (ModuleCat.{u} R) i).obj M) := by
  let P := projectiveResolution M
  let hTensor := moduleTensorChain_preservesSequentialColimits P.complex
  let hExact := moduleCat_hasExactSequentialColimits (R := R)
  let hHomology := chainHomology_preservesSequentialColimits (C := ModuleCat.{u} R) i
  exact preservesColimitsOfShape_of_natIso (torFixedResolutionNatIso M P i).symm

/-- The scalar-restricted actual TorAlg functor is the original ordinary Tor functor. -/
def scalarExtensionTorNatIso (φ : R →+* S) (i : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i ⋙ ModuleCat.restrictScalars.{u} φ ≅
      (Tor (ModuleCat.{u} R) i).obj ((ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of S S)) :=
  (Functor.isoWhiskerRight (derivedModuleBaseChangeHomologyIso φ i) _).symm ≪≫
    derivedModuleBaseChangeTorIso φ i

/-- G7: actual scalar-extension left derived functors preserve arbitrary sequential colimits. -/
lemma torAlg_preservesSequentialColimits (φ : R →+* S) (i : ℕ) :
    PreservesColimitsOfShape ℕ ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) := by
  let hTor := tor_preservesSequentialColimits
    ((ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of S S)) i
  let hComposite := preservesColimitsOfShape_of_natIso (J := ℕ) (scalarExtensionTorNatIso φ i).symm
  let hRestrict : PreservesColimitsOfShape ℕ (ModuleCat.restrictScalars.{u} φ) :=
    ⟨fun {_} ↦ inferInstance⟩
  let hReflect : ReflectsColimitsOfShape ℕ (ModuleCat.restrictScalars.{u} φ) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) (ModuleCat.restrictScalars.{u} φ)

/-- The standard G7 comparison is the colimit-preservation comparison itself. -/
def torAlgSequentialColimitIso (φ : R →+* S) (F : ℕ ⥤ ModuleCat.{u} R) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (colimit F) ≅
      colimit (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) := by
  let := torAlg_preservesSequentialColimits φ i
  exact preservesColimitIso ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) F

/-- Every stage map is carried to the original inclusion in the TorAlg colimit. -/
lemma torAlgSequentialColimitIso_ι (φ : R →+* S) (F : ℕ ⥤ ModuleCat.{u} R) (i n : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).map (colimit.ι F n) ≫
        (torAlgSequentialColimitIso φ F i).hom =
      colimit.ι (F ⋙ (ModuleCat.extendScalars.{u, u, u} φ).leftDerived i) n := by
  let := torAlg_preservesSequentialColimits φ i
  exact ι_preservesColimitIso_hom _ _ n

/-- Vanishing at every stage gives vanishing at the colimit, in the intended BS application. -/
lemma torAlg_colimit_isZero_of_stages (φ : R →+* S) (F : ℕ ⥤ ModuleCat.{u} R) (i : ℕ)
    (h : ∀ n, IsZero (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (F.obj n))) :
    IsZero (((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj (colimit F)) := by
  apply IsZero.of_iso ?_ (torAlgSequentialColimitIso φ F i)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  exact (h n).eq_of_src _ _


end SerrePositivity
