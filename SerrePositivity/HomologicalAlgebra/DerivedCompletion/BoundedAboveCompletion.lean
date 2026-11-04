module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import SerrePositivity.HomologicalAlgebra.BoundedAbove.Derived
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedNonpositiveHom
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # 上に有界な対象の完備化

## 概要

主元導来完備化が上への有界性（同じコホモロジーの上界）を保つことを示して `D⁻` への制限 `boundedAboveDerivedCompletionFunctor` を作り、冪 Koszul の簡約で完備化の同値を判定する。非正の対象の H⁰ の同型を保つこと、完備化の同値が逆元を作り目標のホモロジーが消える次数では源のホモロジーに完備化のスカラーが全射に作用することを与える。

## 方針

塔の一様な厳密上界から holim 模型の上界を得る。

## 規約

旧 `BoundedAboveCompletion`・`BoundedAboveCompletionEquivalence`・`CompletionUpperBound`・`CompletionH0Comparison`・`CompletionHomologyDivisibility`。

## 使われ方

`CompletionMonoidal` 以降、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section BoundedAboveCompletionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- A uniform upper bound on the terms of a tower bounds its product. -/
lemma complexTowerProduct_isStrictlyLE
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : ∀ n, (K n).IsStrictlyLE b) : (piObj K).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have (n : ℕ) : Subsingleton ((K n).X i) := by
    have := hK n
    exact ModuleCat.isZero_iff_subsingleton.mp ((K n).isZero_of_isStrictlyLE b i hi)
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((complexProductDegreeEquiv R K i).injective.subsingleton)

/-- Holim raises a uniform strict upper bound by at most one degree. -/
lemma complexTowerHomotopyLimit_isStrictlyLE
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (b : ℤ) (hK : ∀ n, (K n).IsStrictlyLE b) :
    (complexTowerHomotopyLimit R K t).IsStrictlyLE (b + 1) := by
  have := complexTowerProduct_isStrictlyLE R K b hK
  have hc : (CochainComplex.mappingCone (complexTowerDifference R K t)).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨(piObj K).isZero_of_isStrictlyLE b (i + 1) (by omega),
      (piObj K).isZero_of_isStrictlyLE b i hi⟩
  exact CochainComplex.isStrictlyLE_shift _ b (-1) (b + 1) (by omega)

/-- The actual completion complex of an upper-bounded complex is upper bounded. -/
lemma complexCompletion_isStrictlyLE (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] : ((complexCompletionFunctor R a).obj K).IsStrictlyLE (b + 1) := by
  apply complexTowerHomotopyLimit_isStrictlyLE R _ _ b
  intro n
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE b (i + 1) (by omega), K.isZero_of_isStrictlyLE b i hi⟩

/-- Completion of an actual bounded-above derived object remains bounded above. -/
lemma derivedComplexCompletionFunctor_isBoundedAbove (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ∃ b : ℤ, ((derivedComplexCompletionFunctor R a).obj X.obj).IsLE b := by
  let P := boundedAboveDerivedChosenModel X
  have := complexCompletion_isStrictlyLE R a P.complex P.bound
  let e : DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj P.complex) ≅
      (derivedComplexCompletionFunctor R a).obj X.obj :=
    (derivedComplexCompletionComparison R a).symm.app P.complex ≪≫
      (derivedComplexCompletionFunctor R a).mapIso P.iso
  exact ⟨P.bound + 1, DerivedCategory.TStructure.t.isLE_of_iso e (P.bound + 1)⟩

/-- Restrict actual principal completion to the standard bounded-above derived category. -/
def boundedAboveDerivedCompletionFunctor (a : R) :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ DerivedCategory.Minus (ModuleCat.{u} R) :=
  DerivedCategory.TStructure.t.minus.lift
    (DerivedCategory.Minus.ι ⋙ derivedComplexCompletionFunctor R a)
    (derivedComplexCompletionFunctor_isBoundedAbove R a)

/-- The actual standard completion unit inside the bounded-above derived category. -/
def boundedAboveDerivedCompletionUnit (a : R) :
    𝟭 (DerivedCategory.Minus (ModuleCat.{u} R)) ⟶ boundedAboveDerivedCompletionFunctor R a where
  app X := ObjectProperty.homMk ((derivedComplexCompletionUnit R a).app X.obj)
  naturality {X Y} f := by
    apply InducedCategory.hom_ext
    exact (derivedComplexCompletionUnit R a).naturality f.hom

end SerrePositivity.DerivedCompletion

end BoundedAboveCompletionPart

section BoundedAboveCompletionEquivalencePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- If completion inverts a morphism, every power-Koszul reduction inverts it. -/
theorem derivedScalarCone_map_isIso_of_completion
    {X Y : ConcreteDerivedCategory R} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f)) (n : ℕ) :
    IsIso ((derivedScalarConeFunctor R (a ^ n)).map f) := by
  have := hf
  let G := derivedScalarConeFunctor R (a ^ n)
  let μ := derivedComplexCompletionReduction R a n
  have := derivedComplexCompletionReduction_isIso R a n X
  have := derivedComplexCompletionReduction_isIso R a n Y
  have : IsIso (G.map f ≫ μ.app Y) := by
    rw [μ.naturality f]
    change IsIso (μ.app X ≫ G.map ((derivedComplexCompletionFunctor R a).map f))
    infer_instance
  exact IsIso.of_isIso_comp_right (G.map f) (μ.app Y)

/-- For bounded-above objects, power-Koszul equivalences become completion equivalences. -/
theorem boundedAboveCompletion_map_isIso_of_koszul
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom)) :
    IsIso ((derivedComplexCompletionFunctor R a).map f.hom) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  have hk (n : ℕ) : QuasiIso ((scalarConeFunctor (a ^ n)).map h) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    apply (NatIso.isIso_map_iff (derivedScalarConeComparison R (a ^ n)) h).mp
    change IsIso ((derivedScalarConeFunctor R (a ^ n)).map (DerivedCategory.Q.map h))
    dsimp only [h]
    rw [P.map_Q, Functor.map_comp, Functor.map_comp]
    have := hf n
    infer_instance
  have := complexCompletionFunctor_map_quasiIso_of_koszul R a h hk
  have ht : IsIso ((derivedComplexCompletionFunctor R a).map (DerivedCategory.Q.map h)) :=
    (NatIso.isIso_map_iff (derivedComplexCompletionComparison R a) h).mpr (by
      change IsIso (DerivedCategory.Q.map ((complexCompletionFunctor R a).map h))
      infer_instance)
  dsimp only [h] at ht
  rw [P.map_Q, Functor.map_comp, Functor.map_comp] at ht
  have hs : IsIso ((derivedComplexCompletionFunctor R a).map f.hom ≫
      (derivedComplexCompletionFunctor R a).map Q.iso.inv) :=
    IsIso.of_isIso_comp_left ((derivedComplexCompletionFunctor R a).map P.iso.hom) _
  exact IsIso.of_isIso_comp_right _ ((derivedComplexCompletionFunctor R a).map Q.iso.inv)

/-- The actual completion equivalences are precisely the power-Koszul equivalences on D⁻. -/
theorem boundedAboveCompletion_map_isIso_iff_koszul
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y) :
    IsIso ((derivedComplexCompletionFunctor R a).map f.hom) ↔
      ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom) :=
  ⟨fun hf n ↦ derivedScalarCone_map_isIso_of_completion R a f.hom hf n,
    boundedAboveCompletion_map_isIso_of_koszul R a f⟩

/-- Power-Koszul equivalences between complete bounded-above objects are actual isomorphisms. -/
theorem boundedAbove_isIso_of_koszul_of_isComplete
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hX : IsComplete R a X.obj) (hY : IsComplete R a Y.obj)
    (hf : ∀ n : ℕ, IsIso ((derivedScalarConeFunctor R (a ^ n)).map f.hom)) :
    IsIso f := by
  have := boundedAboveCompletion_map_isIso_of_koszul R a f hf
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a X.obj hX
  have := derivedComplexCompletionUnit_isIso_of_isComplete R a Y.obj hY
  have : IsIso (f.hom ≫ (derivedComplexCompletionUnit R a).app Y.obj) := by
    have hn := (derivedComplexCompletionUnit R a).naturality f.hom
    change f.hom ≫ (derivedComplexCompletionUnit R a).app Y.obj =
      (derivedComplexCompletionUnit R a).app X.obj ≫
        (derivedComplexCompletionFunctor R a).map f.hom at hn
    rw [hn]
    infer_instance
  have : IsIso f.hom := IsIso.of_isIso_comp_right _
    ((derivedComplexCompletionUnit R a).app Y.obj)
  have : IsIso (DerivedCategory.Minus.ι.map f) := this
  exact isIso_of_reflects_iso f DerivedCategory.Minus.ι

end SerrePositivity.DerivedCompletion

end BoundedAboveCompletionEquivalencePart

section CompletionUpperBoundPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

lemma complexPowerKoszulStage_homology_isZero_of_gt
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero (K.homology i)) (n : ℕ) (i : ℤ) (hi : b < i) :
    IsZero ((complexPowerKoszulStage R a K n).homology i) :=
  (SerrePositivity.Cone.exact₃ (smulId (a ^ n) K) i (i + 1) rfl).isZero_of_both_isZero
    (hK i hi) (hK (i + 1) (by omega))

/-- The top homology transition is surjective, even when a is a zero divisor. -/
lemma complexPowerKoszulTransition_homology_top_surjective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : IsZero (K.homology (b + 1))) (n : ℕ) :
    Function.Surjective (homologyMap (complexPowerKoszulTransition R a K n) b) := by
  have he := SerrePositivity.Cone.exact₃ (smulId (a ^ n) K) b (b + 1) rfl
  have hep : Epi (homologyMap (CochainComplex.mappingCone.inr (smulId (a ^ n) K)) b) :=
    he.epi_f (hK.eq_of_tgt _ _)
  have hw := congrArg (fun f ↦ homologyMap f b)
    (complexPowerKoszulInclusion_compatible R a K n)
  rw [homologyMap_comp] at hw
  have ht : Epi (homologyMap (complexPowerKoszulTransition R a K n) b) := epi_of_epi_fac hw
  exact (ModuleCat.epi_iff_surjective _).mp ht

lemma complexCompletion_homology_isZero_of_gt
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero (K.homology i)) (i : ℤ) (hi : b < i) :
    IsZero (((complexCompletionFunctor R a).obj K).homology i) := by
  have hdiff : Function.Surjective (complexTowerHomologyDifference R
      (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K) (i - 1)) := by
    apply moduleTowerDifference_surjective
    intro n
    by_cases ht : i - 1 = b
    · rw [ht]
      exact complexPowerKoszulTransition_homology_top_surjective R a K b
        (hK (b + 1) (by omega)) n
    · intro y
      have hz := complexPowerKoszulStage_homology_isZero_of_gt R a K b hK n (i - 1) (by omega)
      exact ⟨0, (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _⟩
  have hinj := complexTowerMilnorProjection_injective_of_surjective R _ _ i hdiff
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ hinj ?_⟩
  apply Subtype.ext
  funext n
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (complexPowerKoszulStage_homology_isZero_of_gt R a K b hK n i hi)).elim _ _

/-- The actual unbounded derived completion preserves every same upper bound. -/
theorem derivedComplexCompletionFunctor_isLE (X : ConcreteDerivedCategory R) (b : ℤ)
    (hX : X.IsLE b) : ((derivedComplexCompletionFunctor R a).obj X).IsLE b := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK (i : ℤ) (hi : b < i) : IsZero (K.homology i) := by
    have hz := (DerivedCategory.isLE_iff _ _).mp hX i hi
    exact hz.of_iso (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e)
  let ef : DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj K) ≅
      (derivedComplexCompletionFunctor R a).obj X :=
    (derivedComplexCompletionComparison R a).symm.app K ≪≫
      (derivedComplexCompletionFunctor R a).mapIso e
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  have hz := complexCompletion_homology_isZero_of_gt R a K b hK i hi
  have hzQ := hz.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _)
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso ef).isZero_iff.mp hzQ

/-- G11-1: the existing bounded-above completion preserves the same upper bound. -/
theorem boundedAboveDerivedCompletionFunctor_isLE
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (b : ℤ) (hX : X.obj.IsLE b) :
    ((boundedAboveDerivedCompletionFunctor R a).obj X).obj.IsLE b :=
  derivedComplexCompletionFunctor_isLE R a X.obj b hX

end SerrePositivity.DerivedCompletion

end CompletionUpperBoundPart

section CompletionH0ComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- H0 of actual completion has the module reflection property on nonpositive sources. -/
def completionH0HomEquiv (X : ConcreteDerivedCategory R) [X.IsLE 0]
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((derivedComplexCompletionFunctor R a).obj X) ⟶ M) ≃
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X ⟶ M) := by
  letI := derivedComplexCompletionFunctor_isLE R a X 0 inferInstance
  exact (derivedNonpositiveHomToSingleEquiv
    ((derivedComplexCompletionFunctor R a).obj X) M).symm |>.trans
    (derivedComplexCompletionHomEquiv R a X
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) hM) |>.trans
    (derivedNonpositiveHomToSingleEquiv X M)

@[simp] lemma completionH0HomEquiv_apply (X : ConcreteDerivedCategory R) [X.IsLE 0]
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M)
    (g : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((derivedComplexCompletionFunctor R a).obj X) ⟶ M) :
    completionH0HomEquiv R a X M hM g =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionUnit R a).app X) ≫ g := by
  let := derivedComplexCompletionFunctor_isLE R a X 0 inferInstance
  simp only [completionH0HomEquiv, Equiv.trans_apply,
    derivedComplexCompletionHomEquiv_apply, derivedNonpositiveHomToSingleEquiv_precomp,
    Equiv.apply_symm_apply]

lemma completionH0HomEquiv_precomp {X Y : ConcreteDerivedCategory R} [X.IsLE 0] [Y.IsLE 0]
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) (f : X ⟶ Y)
    (g : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((derivedComplexCompletionFunctor R a).obj Y) ⟶ M) :
    completionH0HomEquiv R a X M hM
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
        ((derivedComplexCompletionFunctor R a).map f) ≫ g) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f ≫
        completionH0HomEquiv R a Y M hM g := by
  rw [completionH0HomEquiv_apply, completionH0HomEquiv_apply]
  have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
    ((derivedComplexCompletionUnit R a).naturality f)
  simp only [Functor.map_comp, Functor.id_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]

/-- G11-2 on the original unbounded derived category, for the original morphism f. -/
theorem derivedComplexCompletion_h0_map_isIso {X Y : ConcreteDerivedCategory R} (f : X ⟶ Y)
    (hX : X.IsLE 0) (hY : Y.IsLE 0)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      ((derivedComplexCompletionFunctor R a).map f)) := by
  let := hX
  let := hY
  let := hf
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
  let L := derivedComplexCompletionFunctor R a
  have hpre (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M) :
      Function.Bijective (fun g : H.obj (L.obj Y) ⟶ M ↦ H.map (L.map f) ≫ g) := by
    let E := ((completionH0HomEquiv R a Y M hM).trans
      (Iso.homCongr (asIso (H.map f)).symm (Iso.refl M))).trans
      (completionH0HomEquiv R a X M hM).symm
    have he (g : H.obj (L.obj Y) ⟶ M) : E g = H.map (L.map f) ≫ g := by
      apply (completionH0HomEquiv R a X M hM).injective
      simp only [E, Equiv.trans_apply,
        Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
      erw [Equiv.apply_symm_apply]
      exact (completionH0HomEquiv_precomp R a M hM f g).symm
    have hfun : (E : _ → _) = (fun g ↦ H.map (L.map f) ≫ g) := funext he
    rw [← hfun]
    exact E.bijective
  obtain ⟨g, hg⟩ := (hpre (H.obj (L.obj X))
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a X 0)).2 (𝟙 _)
  have hi := (hpre (H.obj (L.obj Y))
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a Y 0)).1
  have hgf : g ≫ H.map (L.map f) = 𝟙 _ := by
    apply hi
    change H.map (L.map f) ≫ (g ≫ H.map (L.map f)) = H.map (L.map f) ≫ 𝟙 _
    change H.map (L.map f) ≫ g = 𝟙 _ at hg
    rw [← Category.assoc, hg, Category.id_comp, Category.comp_id]
  exact ⟨⟨g, hg, hgf⟩⟩

/-- Exact G11 request for the existing bounded-above functor and the given morphism. -/
theorem boundedAboveDerivedCompletion_h0_map_isIso
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hX : X.obj.IsLE 0) (hY : Y.obj.IsLE 0)
    (hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map f.hom)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).map
      (((boundedAboveDerivedCompletionFunctor R a).map f).hom)) :=
  derivedComplexCompletion_h0_map_isIso R a f.hom hX hY hf

end SerrePositivity.DerivedCompletion

end CompletionH0ComparisonPart

section CompletionHomologyDivisibilityPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- A Koszul equivalence detects scalar divisibility in any degree with zero target homology. -/
lemma cochain_homology_smul_surjective_of_koszul_map_quasiIso {R : Type u} [CommRing R] (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hf : QuasiIso ((scalarConeFunctor a).map f)) (i : ℤ)
    (hL : IsZero (L.homology i)) :
    Function.Surjective (fun x : K.homology i => a • x) := by
  have hn : CochainComplex.mappingCone.inr (smulId a K) ≫ (scalarConeFunctor a).map f =
      f ≫ CochainComplex.mappingCone.inr (smulId a L) := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact scalarConeFunctor_inr_map a f j
  have hh := congrArg (fun g => homologyMap g i) hn
  rw [homologyMap_comp, homologyMap_comp] at hh
  have hzero : homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i = 0 := by
    apply (cancel_mono (homologyMap ((scalarConeFunctor a).map f) i)).mp
    rw [hh]
    simp only [zero_comp]
    rw [hL.eq_of_tgt (homologyMap f i) 0, zero_comp]
  have he := Cone.exact₂ (smulId a K) i
  have hep : Epi (homologyMap (smulId a K) i) := he.epi_f hzero
  have hs := (ModuleCat.epi_iff_surjective _).mp hep
  simp only [smulId, homologyMap_smul, homologyMap_id] at hs
  change Function.Surjective (fun x : K.homology i => a • x) at hs
  exact hs

/-- A completion equivalence gives scalar divisibility on the original actual source homology. -/
lemma boundedAbove_homology_smul_surjective_of_completion_map_isIso
    (R : Type u) [CommRing R] (a : R)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) (i : ℤ)
    (hY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj)) :
    Function.Surjective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj => a • x) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let g := P.map Q f.hom
  have hk : IsIso ((derivedScalarConeFunctor R a).map f.hom) := by
    have hi := derivedScalarCone_map_isIso_of_completion R a f.hom hf 1
    rw [pow_one] at hi
    exact hi
  have hg : QuasiIso ((scalarConeFunctor a).map g) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    apply (NatIso.isIso_map_iff (derivedScalarConeComparison R a) g).mp
    change IsIso ((derivedScalarConeFunctor R a).map (DerivedCategory.Q.map g))
    dsimp only [g]
    rw [P.map_Q, Functor.map_comp, Functor.map_comp]
    have := hk
    infer_instance
  let eP := (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P.complex).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso P.iso).toLinearEquiv
  let eQ := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app Q.complex).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso Q.iso
  have hs := cochain_homology_smul_surjective_of_koszul_map_quasiIso a g hg i (hY.of_iso eQ)
  intro x
  obtain ⟨y, hy⟩ := hs (eP.symm x)
  refine ⟨eP y, ?_⟩
  change a • eP y = x
  change a • y = eP.symm x at hy
  rw [← eP.map_smul, hy, eP.apply_symm_apply]

end SerrePositivity.DerivedCompletion

end CompletionHomologyDivisibilityPart
