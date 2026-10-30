module

public import SerrePositivity.HomologicalAlgebra.LinearYoneda
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.KoszulComparison
public import SerrePositivity.HomologicalAlgebra.ComplexColimits
public import SerrePositivity.HomologicalAlgebra.CoefficientDimensionShift
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.Actions
public import SerrePositivity.HomologicalAlgebra.KoszulDualBaseChange

/-! # Ext の余極限と局所コホモロジー

## 概要

逆系の Ext の余極限を係数複体の列で表し、その係数モデルが完全で入射的な対象で正次数が非輪状であることを示す。選んだ入射的な埋め込みによる次元シフトの自然同型を作り、任意の有限列の Koszul 複体の余極限が局所コホモロジーを計算すること（列の正則性は不要）と、任意の Noether な係数環の変更での局所コホモロジーの比較を与える。

## 方針

両方の係数モデルが完全で入射的に非輪状なので、零次の標準比較が自然な次元シフトで全次数へ延びる。

## 規約

局所コホモロジーは Mathlib の `localCohomology` を使う。

## 使われ方

CLMST の局所コホモロジーの消滅、HomologicalAlgebra の Koszul の局所コホモロジー。
-/

@[expose] public noncomputable section

universe u v v' u'

section ProjectiveExtSequencePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Chosen resolutions are dualized only along adjacent standard lifts.
`Functor.ofSequence` supplies the strictly composable coefficient-complex diagram. -/
def projectiveExtCoefficientDiagram (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    ℕ ⥤ (ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ) :=
  Functor.ofSequence
    (X := fun n => chainLinearYonedaFunctor (projectiveResolution (X.obj (op n))).complex)
    (fun n => chainLinearYonedaMap (ProjectiveResolution.lift
      (X.map (homOfLE (Nat.le_succ n)).op)
      (projectiveResolution (X.obj (op (n + 1)))) (projectiveResolution (X.obj (op n)))))

/-- The ordinary Ext diagram associated to an inverse coefficient-source system. -/
def inverseSystemExtDiagram (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    ℕ ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  opOp ℕ ⋙ X.op ⋙ Ext R (ModuleCat.{u} R) i

/-- Actual homology of the strict coefficient-complex diagram computes Ext,
including all transition maps and arbitrary coefficient morphisms. -/
def projectiveExtCoefficientDiagramHomologyNatIso (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    inverseSystemExtDiagram X i ≅
      projectiveExtCoefficientDiagram X ⋙
        (Functor.whiskeringRight _ _ _).obj (homologyFunctor (ModuleCat.{u} R) (.up ℕ) i) := by
  let α : inverseSystemExtDiagram X i ⟶
      projectiveExtCoefficientDiagram X ⋙
        (Functor.whiskeringRight _ _ _).obj (homologyFunctor (ModuleCat.{u} R) (.up ℕ) i) :=
    NatTrans.ofSequence (fun n => (projectiveResolutionExtNatIso
      (projectiveResolution (X.obj (op n))) i).hom) (by
        intro n
        simp only [inverseSystemExtDiagram, projectiveExtCoefficientDiagram,
          Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
          Functor.whiskeringRight_obj_map]
        apply NatTrans.ext
        funext M
        exact projectiveResolutionIsoExt_first_naturality
          (X.map (homOfLE (Nat.le_succ n)).op)
          (projectiveResolution (X.obj (op (n + 1))))
          (projectiveResolution (X.obj (op n))) _
          (ProjectiveResolution.lift_commutes_zero _ _ _) M i)
  exact NatIso.ofComponents
    (fun n => projectiveResolutionExtNatIso (projectiveResolution (X.obj (op n))) i)
    (fun f => α.naturality f)

local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- The strict Ext model as a diagram of complexes of coefficient functors. -/
def projectiveExtFunctorComplexDiagram (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  projectiveExtCoefficientDiagram X ⋙
    functorCochainComplexFunctor (ModuleCat.{u} R) (ModuleCat.{u} R)

/-- The actual coefficient-complex colimit realizing inverse-system Ext. -/
def projectiveExtColimitComplex (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R ⥤ ModuleCat.{u} R) ℕ :=
  colimit (projectiveExtFunctorComplexDiagram X)

/-- Exact sequential colimits identify the homology of the actual model
with the entire Ext colimit, naturally in arbitrary coefficients. -/
def projectiveExtColimitHomologyNatIso (X : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    (projectiveExtColimitComplex X).homology i ≅ colimit (inverseSystemExtDiagram X i) :=
  sequentialCochainHomologyColimitIso (projectiveExtFunctorComplexDiagram X) i ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft (projectiveExtCoefficientDiagram X)
      (functorCochainHomologyNatIso (ModuleCat.{u} R) (ModuleCat.{u} R) i)) ≪≫
    (HasColimit.isoOfNatIso (projectiveExtCoefficientDiagramHomologyNatIso X i)).symm

end SerrePositivity

end ProjectiveExtSequencePart

section ProjectiveExtColimitExactPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
variable {R : Type u} [CommRing R] (X : ℕᵒᵖ ⥤ ModuleCat.{u} R)
local instance : AB5OfSize.{0, 0} (ModuleCat.{u} R) :=
  AB5OfSize_of_univLE (ModuleCat.{u} R)

/-- Read the actual Ext colimit complex as a coefficient functor. -/
def projectiveExtColimitFunctor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℕ :=
  (projectiveExtColimitComplex X).asFunctor

instance projectiveExtColimitTerm_preservesFiniteLimits (i : ℕ) :
    PreservesFiniteLimits ((projectiveExtColimitComplex X).X i) := by
  let D := projectiveExtFunctorComplexDiagram X ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteLimits (D.obj n) := fun n => by
    change PreservesFiniteLimits (chainLinearYonedaFunctor
      (projectiveResolution (X.obj (op n))).complex ⋙ eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteLimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (projectiveExtFunctorComplexDiagram X)).symm

instance projectiveExtColimitTerm_preservesFiniteColimits (i : ℕ) :
    PreservesFiniteColimits ((projectiveExtColimitComplex X).X i) := by
  let D := projectiveExtFunctorComplexDiagram X ⋙
    eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i
  have : ∀ n, PreservesFiniteColimits (D.obj n) := fun n => by
    change PreservesFiniteColimits (chainLinearYonedaFunctor
      (projectiveResolution (X.obj (op n))).complex ⋙ eval (ModuleCat.{u} R) (.up ℕ) i)
    infer_instance
  exact preservesFiniteColimits_of_natIso (preservesColimitIso
    (eval (ModuleCat.{u} R ⥤ ModuleCat.{u} R) (.up ℕ) i)
    (projectiveExtFunctorComplexDiagram X)).symm

instance projectiveExtColimitFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (projectiveExtColimitFunctor X) where
  preservesFiniteLimits J _ _ :=
    preservesLimitsOfShape_of_eval _ (fun i => by
      change PreservesLimitsOfShape J ((projectiveExtColimitComplex X).X i)
      infer_instance)

instance projectiveExtColimitFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (projectiveExtColimitFunctor X) where
  preservesFiniteColimits J _ _ :=
    preservesColimitsOfShape_of_eval _ (fun i => by
      change PreservesColimitsOfShape J ((projectiveExtColimitComplex X).X i)
      infer_instance)

/-- The actual colimit complex computes the Ext colimit in every degree. -/
def projectiveExtColimitFunctorHomologyNatIso (i : ℕ) :
    projectiveExtColimitFunctor X ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      colimit (inverseSystemExtDiagram X i) :=
  asFunctorCochainHomologyIso (projectiveExtColimitComplex X) i ≪≫
    projectiveExtColimitHomologyNatIso X i

/-- The actual Ext coefficient colimit has no positive homology on injectives. -/
lemma projectiveExtColimitFunctor_injective_positive_homology_isZero
    (J : ModuleCat.{u} R) [Injective J] (i : ℕ) (hi : 0 < i) :
    IsZero (((projectiveExtColimitFunctor X).obj J).homology i) := by
  let E := (projectiveExtColimitFunctorHomologyNatIso X i).app J ≪≫
    colimitObjIsoColimitCompEvaluation (inverseSystemExtDiagram X i) J
  apply IsZero.of_iso _ E
  apply sequentialModuleColimit_isZero_of_eventually_zero
  intro n
  refine ⟨n, le_refl n, ?_⟩
  have hz : IsZero (((Ext R (ModuleCat.{u} R) i).obj (op (X.obj (op n)))).obj J) :=
    IsZero.of_iso
      (projectiveResolution_injective_dual_positive_homology_isZero
        (projectiveResolution (X.obj (op n))) J i hi)
      ((projectiveResolution (X.obj (op n))).isoExt i J)
  exact hz.eq_zero_of_src _

end SerrePositivity

end ProjectiveExtColimitExactPart

section InjectiveCoefficientDimensionShiftPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The short exact sequence associated to the chosen injective embedding. -/
abbrev injectiveCoefficientSequence (M : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (by simp)

lemma injectiveCoefficientSequence_shortExact (M : C) :
    (injectiveCoefficientSequence M).ShortExact where
  exact := ShortComplex.exact_cokernel _

/-- Any coefficient map extends to a map of the chosen short exact sequences.
The extensions are not asserted to form a functor. -/
def injectiveCoefficientSequenceMap {M N : C} (f : M ⟶ N) :
    injectiveCoefficientSequence M ⟶ injectiveCoefficientSequence N where
  τ₁ := f
  τ₂ := Injective.factorThru (f ≫ Injective.ι N) (Injective.ι M)
  τ₃ := cokernel.map _ _ f
    (Injective.factorThru (f ≫ Injective.ι N) (Injective.ι M)) (by simp)
  comm₁₂ := by simp [injectiveCoefficientSequence]
  comm₂₃ := by simp [injectiveCoefficientSequence]

variable (F G : C ⥤ CochainComplex D ℕ)
variable [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Exact coefficient functors preserve the chosen injective short exact sequence. -/
lemma injectiveCoefficientSequence_map_shortExact (M : C) :
    ((injectiveCoefficientSequence M).map F).ShortExact :=
  (injectiveCoefficientSequence_shortExact M).map_of_exact F

/-- Lift a natural homology comparison by one degree using positive acyclicity
on injective coefficients. The construction also handles the first step. -/
def injectiveCoefficientHomologyStep (n : ℕ)
    (hF : ∀ J : C, Injective J → IsZero ((F.obj J).homology (n + 1)))
    (hG : ∀ J : C, Injective J → IsZero ((G.obj J).homology (n + 1)))
    (e : F ⋙ homologyFunctor D (.up ℕ) n ≅ G ⋙ homologyFunctor D (.up ℕ) n) :
    F ⋙ homologyFunctor D (.up ℕ) (n + 1) ≅
      G ⋙ homologyFunctor D (.up ℕ) (n + 1) :=
  NatIso.ofComponents (fun M => coefficientDimensionShiftIso
    (injectiveCoefficientSequence_map_shortExact F M) n
    (injectiveCoefficientSequence_map_shortExact G M)
    (hF (Injective.under M) inferInstance) (hG (Injective.under M) inferInstance)
    (e.app (Injective.under M)) (e.app (cokernel (Injective.ι M)))
    (e.hom.naturality (cokernel.π (Injective.ι M)))) (by
      intro M N f
      apply coefficientDimensionShift_naturality
        (injectiveCoefficientSequence_map_shortExact F M) n
        (injectiveCoefficientSequence_map_shortExact F N)
        (injectiveCoefficientSequence_map_shortExact G M)
        (injectiveCoefficientSequence_map_shortExact G N)
        (hF (Injective.under M) inferInstance)
        (F.mapShortComplex.map (injectiveCoefficientSequenceMap f))
        (G.mapShortComplex.map (injectiveCoefficientSequenceMap f))
      · exact coefficientDimensionShiftIso_δ _ _ _ _ _ _ _ _
      · exact coefficientDimensionShiftIso_δ _ _ _ _ _ _ _ _
      · exact e.hom.naturality (injectiveCoefficientSequenceMap f).τ₃)

/-- The one-step lift agrees with the given lower comparison on the actual
connecting map of the chosen injective short exact sequence. -/
@[reassoc]
lemma injectiveCoefficientHomologyStep_δ (n : ℕ)
    (hF : ∀ J : C, Injective J → IsZero ((F.obj J).homology (n + 1)))
    (hG : ∀ J : C, Injective J → IsZero ((G.obj J).homology (n + 1)))
    (e : F ⋙ homologyFunctor D (.up ℕ) n ≅ G ⋙ homologyFunctor D (.up ℕ) n)
    (M : C) :
    (injectiveCoefficientSequence_map_shortExact F M).δ n (n + 1) rfl ≫
        ((injectiveCoefficientHomologyStep F G n hF hG e).app M).hom =
      (e.app (cokernel (Injective.ι M))).hom ≫
        (injectiveCoefficientSequence_map_shortExact G M).δ n (n + 1) rfl :=
  coefficientDimensionShiftIso_δ
    (injectiveCoefficientSequence_map_shortExact F M) n
    (injectiveCoefficientSequence_map_shortExact G M)
    (hF (Injective.under M) inferInstance) (hG (Injective.under M) inferInstance)
    (e.app (Injective.under M)) (e.app (cokernel (Injective.ι M)))
    (e.hom.naturality (cokernel.π (Injective.ι M)))

/-- Positive injective acyclicity and a natural zero-degree comparison determine
natural homology isomorphisms in every degree. -/
def injectiveCoefficientHomologyNatIso
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0) :
    ∀ n : ℕ, F ⋙ homologyFunctor D (.up ℕ) n ≅ G ⋙ homologyFunctor D (.up ℕ) n
  | 0 => e₀
  | n + 1 => injectiveCoefficientHomologyStep F G n
      (fun J hJ => hF J hJ (n + 1) (Nat.zero_lt_succ n))
      (fun J hJ => hG J hJ (n + 1) (Nat.zero_lt_succ n))
      (injectiveCoefficientHomologyNatIso hF hG e₀ n)

/-- The recursive comparison recovers the prescribed zero-degree comparison. -/
@[simp]
lemma injectiveCoefficientHomologyNatIso_zero
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0) :
    injectiveCoefficientHomologyNatIso F G hF hG e₀ 0 = e₀ := rfl

/-- The recursive comparison is compatible with dimension shifting at every step. -/
@[reassoc]
lemma injectiveCoefficientHomologyNatIso_δ
    (hF : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((F.obj J).homology n))
    (hG : ∀ J : C, Injective J → ∀ n : ℕ, 0 < n → IsZero ((G.obj J).homology n))
    (e₀ : F ⋙ homologyFunctor D (.up ℕ) 0 ≅ G ⋙ homologyFunctor D (.up ℕ) 0)
    (n : ℕ) (M : C) :
    (injectiveCoefficientSequence_map_shortExact F M).δ n (n + 1) rfl ≫
        ((injectiveCoefficientHomologyNatIso F G hF hG e₀ (n + 1)).app M).hom =
      ((injectiveCoefficientHomologyNatIso F G hF hG e₀ n).app
        (cokernel (Injective.ι M))).hom ≫
        (injectiveCoefficientSequence_map_shortExact G M).δ n (n + 1) rfl :=
  injectiveCoefficientHomologyStep_δ F G n _ _ _ M

end SerrePositivity

end InjectiveCoefficientDimensionShiftPart

section GeneralKoszulLocalCohomologyPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {e : ℕ} (z : Fin e → R)

/-- The actual projective-resolution colimit for coordinate-power quotients
computes Mathlib local cohomology naturally in all coefficients and degrees. -/
def projectiveExtPowerQuotientLocalCohomologyNatIso (i : ℕ) :
    projectiveExtColimitFunctor
        (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)) ⋙
      homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
        localCohomology (Ideal.span (Set.range z)) i :=
  projectiveExtColimitFunctorHomologyNatIso _ i ≪≫
    Functor.Final.colimitIso (opOp ℕ) (localCohomology.diagram (powerKoszulIdealDiagram z) i) ≪≫
      localCohomologyPowerKoszulIdealNatIso z i

/-- An arbitrary finite sequence in a Noetherian ring computes actual local
cohomology by its actual dual power-Koszul colimit, naturally in coefficients. -/
def generalKoszulLocalCohomologyComparison (i : ℕ) :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) i ≅
      localCohomology (Ideal.span (Set.range z)) i :=
  injectiveCoefficientHomologyNatIso
    (koszulDualColimitFunctor z)
    (projectiveExtColimitFunctor (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)))
    (fun J hJ n hn => by
      have : Injective J := hJ
      exact koszulDualColimit_injective_positive_homology_isZero z J n hn)
    (fun J hJ n hn => by
      have : Injective J := hJ
      exact projectiveExtColimitFunctor_injective_positive_homology_isZero _ J n hn)
    (koszulDualColimitZeroLocalCohomologyNatIso z ≪≫
      (projectiveExtPowerQuotientLocalCohomologyNatIso z 0).symm) i ≪≫
    projectiveExtPowerQuotientLocalCohomologyNatIso z i

end SerrePositivity

end GeneralKoszulLocalCohomologyPart

section GeneralLocalCohomologyBaseChangePart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S]
variable {e : ℕ} (z : Fin e → R)

section Algebra
variable [Algebra R S]

local instance : Functor.PreservesHomology
    ((Functor.whiskeringRight (ModuleCat.{u} S) (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R S))) where
  preservesKernels f := by infer_instance
  preservesCokernels f := by infer_instance

/-- Restriction compares actual coefficient-algebra colimit homology with
the original Koszul homology functor, before any local cohomology computation. -/
def algebraKoszulColimitHomologyRestrictNatIso (i : ℕ) :
    (algebraKoszulDualColimitComplex (C := S) z).homology i ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      ModuleCat.restrictScalars (algebraMap R S) ⋙ (koszulDualColimitComplex z).homology i :=
  (((algebraKoszulDualColimitComplex (C := S) z).sc i).mapHomologyIso
    ((Functor.whiskeringRight (ModuleCat.{u} S) (ModuleCat.{u} S) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R S)))).symm ≪≫
    (homologyFunctor (ModuleCat.{u} S ⥤ ModuleCat.{u} R) (.up ℕ) i).mapIso
      (algebraKoszulDualColimitRestrictIso (C := S) z) ≪≫
    ((koszulDualColimitComplex z).sc i).mapHomologyIso
      ((Functor.whiskeringLeft (ModuleCat.{u} S) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R S)))

/-- Arbitrary finite sequences compute local cohomology with its actual
coefficient-algebra action after restriction, without a regularity assumption. -/
def generalAlgebraKoszulColimitLocalCohomologyNatIso [IsNoetherianRing R] (i : ℕ) :
    (algebraKoszulDualColimitComplex (C := S) z).homology i ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      ModuleCat.restrictScalars (algebraMap R S) ⋙
        localCohomology (Ideal.span (Set.range z)) i :=
  algebraKoszulColimitHomologyRestrictNatIso z i ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars (algebraMap R S))
      ((asFunctorCochainHomologyIso (koszulDualColimitComplex z) i).symm ≪≫
        generalKoszulLocalCohomologyComparison z i)

/-- Actual local cohomology is independent of the coefficient ring, with
support extended along the ring map. No flatness is required. -/
def localCohomologyAlgebraRestrictScalarsNatIso
    [IsNoetherianRing R] [IsNoetherianRing S] (i : ℕ) :
    ModuleCat.restrictScalars (algebraMap R S) ⋙
        localCohomology (Ideal.span (Set.range z)) i ≅
      localCohomology (Ideal.span (Set.range ((algebraMap R S) ∘ z))) i ⋙
        ModuleCat.restrictScalars (algebraMap R S) :=
  (generalAlgebraKoszulColimitLocalCohomologyNatIso (S := S) z i).symm ≪≫
    Functor.isoWhiskerRight
      ((homologyFunctor (ModuleCat.{u} S ⥤ ModuleCat.{u} S) (.up ℕ) i).mapIso
        (koszulDualColimitBaseChangeIso (S := S) z).symm)
      (ModuleCat.restrictScalars (algebraMap R S)) ≪≫
    Functor.isoWhiskerRight
      ((asFunctorCochainHomologyIso
        (koszulDualColimitComplex ((algebraMap R S) ∘ z)) i).symm ≪≫
          generalKoszulLocalCohomologyComparison ((algebraMap R S) ∘ z) i)
      (ModuleCat.restrictScalars (algebraMap R S))

end Algebra

/-- Ring-homomorphism form of actual all-degree local cohomology ring change. -/
def localCohomologyRestrictScalarsNatIso [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (i : ℕ) :
    ModuleCat.restrictScalars φ ⋙ localCohomology (Ideal.span (Set.range z)) i ≅
      localCohomology (Ideal.span (Set.range (φ ∘ z))) i ⋙ ModuleCat.restrictScalars φ := by
  letI := φ.toAlgebra
  exact localCohomologyAlgebraRestrictScalarsNatIso (S := S) z i

/-- Support can be replaced by any ideal with the same extended radical,
including a maximal ideal, in every degree. -/
def localCohomologyRestrictScalarsSupportNatIso [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R →+* S) (J : Ideal S)
    (h : ((Ideal.span (Set.range z)).map φ).radical = J.radical) (i : ℕ) :
    ModuleCat.restrictScalars φ ⋙ localCohomology (Ideal.span (Set.range z)) i ≅
      localCohomology J i ⋙ ModuleCat.restrictScalars φ := by
  have hspan : Ideal.span (Set.range (φ ∘ z)) = (Ideal.span (Set.range z)).map φ := by
    rw [Ideal.map_span, ← Set.range_comp]
  have h' : (Ideal.span (Set.range (φ ∘ z))).radical = J.radical := by
    rw [hspan]
    exact h
  exact localCohomologyRestrictScalarsNatIso z φ i ≪≫
    Functor.isoWhiskerRight (localCohomology.isoOfSameRadical h' i)
      (ModuleCat.restrictScalars φ)

/-- The all-degree ring/support comparison preserves and reflects zero induced
maps of arbitrary coefficient modules. -/
lemma localCohomologyRestrictScalarsSupport_map_eq_zero_iff
    [IsNoetherianRing R] [IsNoetherianRing S] (φ : R →+* S) (J : Ideal S)
    (h : ((Ideal.span (Set.range z)).map φ).radical = J.radical) (i : ℕ)
    {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    (localCohomology (Ideal.span (Set.range z)) i).map
        ((ModuleCat.restrictScalars φ).map f) = 0 ↔
      (localCohomology J i).map f = 0 := by
  let E := localCohomologyRestrictScalarsSupportNatIso z φ J h i
  have hn := E.hom.naturality f
  constructor
  · intro hf
    have hz : (ModuleCat.restrictScalars φ).map ((localCohomology J i).map f) = 0 := by
      apply (cancel_epi (E.app M).hom).mp
      simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom, hf, zero_comp, comp_zero]
        using hn.symm
    exact ((ModuleCat.restrictScalars φ).map_eq_zero_iff).mp hz
  · intro hf
    apply (cancel_mono (E.app N).hom).mp
    simpa only [Functor.comp_map, Functor.comp_obj, Iso.app_hom, hf, Functor.map_zero,
      zero_comp, comp_zero] using hn

end SerrePositivity

end GeneralLocalCohomologyBaseChangePart
