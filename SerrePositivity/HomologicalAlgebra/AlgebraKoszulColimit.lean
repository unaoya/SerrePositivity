module
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulDual
public import SerrePositivity.HomologicalAlgebra.LinearFunctorColimits
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyTorAnnihilator
public import SerrePositivity.HomologicalAlgebra.LocalCohomologyKoszulComparison
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Actual coefficient-algebra Koszul colimits and their local-cohomology comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {e : ℕ} (z : Fin e → R)

/-- The coefficient-algebra dual power diagram as complexes of coefficient functors. -/
def algebraKoszulDualFunctorComplexDiagram :
    ℕ ⥤ CochainComplex (ModuleCat.{u} C ⥤ ModuleCat.{u} C) ℕ :=
  algebraKoszulDualPowerDiagram (C := C) z ⋙
    functorCochainComplexFunctor (ModuleCat.{u} C) (ModuleCat.{u} C)

/-- The actual C-module complex colimit, retaining all coefficient morphisms. -/
def algebraKoszulDualColimitComplex : CochainComplex (ModuleCat.{u} C ⥤ ModuleCat.{u} C) ℕ :=
  colimit (algebraKoszulDualFunctorComplexDiagram (C := C) z)

/-- Read the actual colimit as C-module complexes depending on C-module coefficients. -/
def algebraKoszulDualColimitFunctor : ModuleCat.{u} C ⥤ CochainComplex (ModuleCat.{u} C) ℕ :=
  (algebraKoszulDualColimitComplex (C := C) z).asFunctor

/-- Each term of the actual colimit remains additive in its C-module coefficients. -/
instance algebraKoszulDualColimitTerm_additive (i : ℕ) :
    ((algebraKoszulDualColimitComplex (C := C) z).X i).Additive := by
  let D := algebraKoszulDualFunctorComplexDiagram (C := C) z ⋙
    eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i
  have : ∀ n, (D.obj n).Additive := fun n =>
    { map_add := by
        intro M N f g
        change ((algebraKoszulDualFunctor (C := C) (fun j => z j ^ n)).map (f + g)).f i =
          ((algebraKoszulDualFunctor (C := C) (fun j => z j ^ n)).map f).f i +
            ((algebraKoszulDualFunctor (C := C) (fun j => z j ^ n)).map g).f i
        simp only [Functor.map_add, HomologicalComplex.add_f_apply] }
  let E := preservesColimitIso
    (eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i)
    (algebraKoszulDualFunctorComplexDiagram (C := C) z)
  exact Functor.additive_of_iso E.symm

/-- Each colimit term has the actual linear coefficient action over C. -/
instance algebraKoszulDualColimitTerm_linear (i : ℕ) :
    Functor.Linear C ((algebraKoszulDualColimitComplex (C := C) z).X i) := by
  let D := algebraKoszulDualFunctorComplexDiagram (C := C) z ⋙
    eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i
  have : ∀ n, Functor.Linear C (D.obj n) := fun n =>
    { map_smul := by
        intro M N f c
        change ((algebraKoszulDualFunctor (C := C) (fun j => z j ^ n)).map (c • f)).f i =
          c • ((algebraKoszulDualFunctor (C := C) (fun j => z j ^ n)).map f).f i
        simp only [Functor.map_smul, HomologicalComplex.smul_f_apply] }
  let E := preservesColimitIso
    (eval (ModuleCat.{u} C ⥤ ModuleCat.{u} C) (.up ℕ) i)
    (algebraKoszulDualFunctorComplexDiagram (C := C) z)
  exact Functor.linear_of_iso C E.symm

/-- The complex colimit is additive in all coefficient maps. -/
instance algebraKoszulDualColimitFunctor_additive :
    (algebraKoszulDualColimitFunctor (C := C) z).Additive where
  map_add {M N f g} := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact ((algebraKoszulDualColimitComplex (C := C) z).X i).map_add

/-- Scalar multiplication on coefficients induces the actual scalar map on the C-complex. -/
instance algebraKoszulDualColimitFunctor_linear :
    Functor.Linear C (algebraKoszulDualColimitFunctor (C := C) z) where
  map_smul f c := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact ((algebraKoszulDualColimitComplex (C := C) z).X i).map_smul c f

/-- The full power diagrams agree after coefficient restriction, with all power transitions. -/
def algebraKoszulDualPowerRestrictDiagramNatIso :
    algebraKoszulDualPowerDiagram (C := C) z ⋙
        (Functor.whiskeringRight (ModuleCat.{u} C) (CochainComplex (ModuleCat.{u} C) ℕ)
          (CochainComplex (ModuleCat.{u} R) ℕ)).obj
            ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℕ)) ≅
      koszulDualPowerDiagram z ⋙
        (Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R)
          (CochainComplex (ModuleCat.{u} R) ℕ)).obj
            (ModuleCat.restrictScalars (algebraMap R C)) := by
  let η : algebraKoszulDualPowerDiagram (C := C) z ⋙
      (Functor.whiskeringRight (ModuleCat.{u} C) (CochainComplex (ModuleCat.{u} C) ℕ)
        (CochainComplex (ModuleCat.{u} R) ℕ)).obj
          ((ModuleCat.restrictScalars (algebraMap R C)).mapHomologicalComplex (.up ℕ)) ⟶
    koszulDualPowerDiagram z ⋙
      (Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R)
        (CochainComplex (ModuleCat.{u} R) ℕ)).obj (ModuleCat.restrictScalars (algebraMap R C)) :=
    NatTrans.ofSequence
    (fun n => (algebraKoszulDualRestrictNatIso (C := C) (fun j => z j ^ n)).hom) (by
      intro n
      simp only [algebraKoszulDualPowerDiagram, koszulDualPowerDiagram,
        Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
        Functor.whiskeringRight_obj_map, Functor.whiskeringLeft_obj_map]
      exact algebraKoszulDualRestrictNatIso_power_transition (C := C) z n)
  exact NatIso.ofComponents
    (fun n => algebraKoszulDualRestrictNatIso (C := C) (fun j => z j ^ n))
    (fun f => η.naturality f)

/-- The transposed diagrams also agree under actual post- and precomposition of coefficients. -/
def algebraKoszulDualComplexRestrictDiagramNatIso :
    algebraKoszulDualFunctorComplexDiagram (C := C) z ⋙
        ((Functor.whiskeringRight (ModuleCat.{u} C) (ModuleCat.{u} C) (ModuleCat.{u} R)).obj
          (ModuleCat.restrictScalars (algebraMap R C))).mapHomologicalComplex (.up ℕ) ≅
      koszulDualFunctorComplexDiagram z ⋙
        ((Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
          (ModuleCat.restrictScalars (algebraMap R C))).mapHomologicalComplex (.up ℕ) :=
  Functor.isoWhiskerRight (algebraKoszulDualPowerRestrictDiagramNatIso (C := C) z)
    (functorCochainComplexFunctor (ModuleCat.{u} C) (ModuleCat.{u} R))

/-- Restriction preserves the actual complex colimit and compares it with the existing R-model. -/
def algebraKoszulDualColimitRestrictIso :
    (((Functor.whiskeringRight (ModuleCat.{u} C) (ModuleCat.{u} C) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R C))).mapHomologicalComplex (.up ℕ)).obj
        (algebraKoszulDualColimitComplex (C := C) z) ≅
      (((Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R C))).mapHomologicalComplex (.up ℕ)).obj
        (koszulDualColimitComplex z) :=
  preservesColimitIso
      (((Functor.whiskeringRight (ModuleCat.{u} C) (ModuleCat.{u} C) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R C))).mapHomologicalComplex (.up ℕ))
      (algebraKoszulDualFunctorComplexDiagram (C := C) z) ≪≫
    HasColimit.isoOfNatIso (algebraKoszulDualComplexRestrictDiagramNatIso (C := C) z) ≪≫
    (preservesColimitIso
      (((Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R C))).mapHomologicalComplex (.up ℕ))
      (koszulDualFunctorComplexDiagram z)).symm

-- Only kernels and cokernels are required; their index categories are small.
local instance : Functor.PreservesHomology
    ((Functor.whiskeringRight (ModuleCat.{u} C) (ModuleCat.{u} C) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R C))) where
  preservesKernels f := by infer_instance
  preservesCokernels f := by infer_instance

/-- The actual C-module homology computes local cohomology after restriction to R. -/
def algebraKoszulDualColimitHomologyNatIso [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    (algebraKoszulDualColimitComplex (C := C) z).homology i ⋙
        ModuleCat.restrictScalars (algebraMap R C) ≅
      ModuleCat.restrictScalars (algebraMap R C) ⋙ localCohomology (Ideal.span (Set.range z)) i :=
  (((algebraKoszulDualColimitComplex (C := C) z).sc i).mapHomologyIso
    ((Functor.whiskeringRight (ModuleCat.{u} C) (ModuleCat.{u} C) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R C)))).symm ≪≫
    (homologyFunctor (ModuleCat.{u} C ⥤ ModuleCat.{u} R) (.up ℕ) i).mapIso
      (algebraKoszulDualColimitRestrictIso (C := C) z) ≪≫
    ((koszulDualColimitComplex z).sc i).mapHomologyIso
      ((Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
        (ModuleCat.restrictScalars (algebraMap R C))) ≪≫
    ((Functor.whiskeringLeft (ModuleCat.{u} C) (ModuleCat.{u} R) (ModuleCat.{u} R)).obj
      (ModuleCat.restrictScalars (algebraMap R C))).mapIso
        (koszulDualColimitHomologyNatIso z hres i)

/-- The comparison is natural in all C-module coefficients for the actual C-complex colimit. -/
def algebraKoszulLocalCohomologyComparison [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    algebraKoszulDualColimitFunctor (C := C) z ⋙
        homologyFunctor (ModuleCat.{u} C) (.up ℕ) i ⋙ ModuleCat.restrictScalars (algebraMap R C) ≅
      ModuleCat.restrictScalars (algebraMap R C) ⋙ localCohomology (Ideal.span (Set.range z)) i :=
  Functor.isoWhiskerRight
      (asFunctorCochainHomologyIso (algebraKoszulDualColimitComplex (C := C) z) i)
      (ModuleCat.restrictScalars (algebraMap R C)) ≪≫
    algebraKoszulDualColimitHomologyNatIso (C := C) z hres i

/-- Identify the restricted regular C-module with its given R-algebra module. -/
def algebraKoszulCoefficientRestrictIso :
    (ModuleCat.restrictScalars (algebraMap R C)).obj (ModuleCat.of C C) ≅ ModuleCat.of R C :=
  (LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of R C)
    (X₂ := (ModuleCat.restrictScalars (algebraMap R C)).obj (ModuleCat.of C C))
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change r • x = algebraMap R C r * x
        exact Algebra.smul_def r x }).symm

/-- Specialize the natural comparison to the coefficient algebra with its original R-action. -/
def algebraKoszulLocalCohomologyAlgebraIso [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap R C)).obj
        (((algebraKoszulDualColimitFunctor (C := C) z).obj (ModuleCat.of C C)).homology i) ≅
      HomologicalAlgebra.localCohomologyModule (Ideal.span (Set.range z)) i C :=
  (algebraKoszulLocalCohomologyComparison (C := C) z hres i).app (ModuleCat.of C C) ≪≫
    (localCohomology (Ideal.span (Set.range z)) i).mapIso
      (algebraKoszulCoefficientRestrictIso (R := R) (C := C))

/-- The actual C-scalar action on colimit homology matches the concrete local-cohomology action. -/
lemma algebraKoszulLocalCohomologyComparison_coefficient_scalar [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) (c : C) :
    (ModuleCat.restrictScalars (algebraMap R C)).map
        (c • 𝟙 (((algebraKoszulDualColimitFunctor (C := C) z).obj (ModuleCat.of C C)).homology i)) ≫
        (algebraKoszulLocalCohomologyAlgebraIso (C := C) z hres i).hom =
      (algebraKoszulLocalCohomologyAlgebraIso (C := C) z hres i).hom ≫
        HomologicalAlgebra.localCohomologyScalarEndomorphism (Ideal.span (Set.range z)) i C c := by
  have h := (algebraKoszulLocalCohomologyComparison (C := C) z hres i).hom.naturality
    (c • 𝟙 (ModuleCat.of C C))
  have hf := (algebraKoszulDualColimitFunctor (C := C) z).map_smul c (𝟙 (ModuleCat.of C C))
  rw [(algebraKoszulDualColimitFunctor (C := C) z).map_id] at hf
  change (ModuleCat.restrictScalars (algebraMap R C)).map
      (homologyMap ((algebraKoszulDualColimitFunctor (C := C) z).map
        (c • 𝟙 (ModuleCat.of C C))) i) ≫
      (algebraKoszulLocalCohomologyComparison (C := C) z hres i).hom.app (ModuleCat.of C C) = _ at h
  rw [hf, homologyMap_smul, HomologicalComplex.homologyMap_id] at h
  dsimp only [algebraKoszulLocalCohomologyAlgebraIso, Iso.trans_hom]
  change _ ≫ ((algebraKoszulLocalCohomologyComparison (C := C) z hres i).hom.app
    (ModuleCat.of C C) ≫ _) = _
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  apply congrArg (fun f =>
    (algebraKoszulLocalCohomologyComparison (C := C) z hres i).hom.app
      (ModuleCat.of C C) ≫ f)
  change (localCohomology (Ideal.span (Set.range z)) i).map _ ≫
      (localCohomology (Ideal.span (Set.range z)) i).map _ =
    (localCohomology (Ideal.span (Set.range z)) i).map _ ≫
      (localCohomology (Ideal.span (Set.range z)) i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (localCohomology (Ideal.span (Set.range z)) i).map
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Faithful coefficient restriction reflects zero scalar action on the actual C-module homology. -/
lemma algebraKoszulLocalCohomology_coefficient_scalar_eq_zero_iff [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (i : ℕ) (c : C) :
    HomologicalAlgebra.localCohomologyScalarEndomorphism (Ideal.span (Set.range z)) i C c = 0 ↔
      c • 𝟙 (((algebraKoszulDualColimitFunctor (C := C) z).obj
        (ModuleCat.of C C)).homology i) = 0 := by
  have h := algebraKoszulLocalCohomologyComparison_coefficient_scalar (C := C) z hres i c
  let E := algebraKoszulLocalCohomologyAlgebraIso (C := C) z hres i
  constructor
  · intro hc
    apply (ModuleCat.restrictScalars (algebraMap R C)).map_injective
    rw [Functor.map_zero]
    apply (cancel_mono E.hom).mp
    rw [h, hc, comp_zero, zero_comp]
  · intro hc
    apply (cancel_epi E.hom).mp
    rw [← h, hc, Functor.map_zero, zero_comp, comp_zero]

/-- Higher Tor annihilation gives an honest ideal annihilator of low C-module colimit homology. -/
lemma algebraKoszulDualColimitHomology_annihilator_of_tor_annihilated [IsNoetherian R R]
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : i < e) :
    I ≤ Module.annihilator C
      (((algebraKoszulDualColimitFunctor (C := C) z).obj (ModuleCat.of C C)).homology i) := by
  intro c hc
  have h := (algebraKoszulLocalCohomology_coefficient_scalar_eq_zero_iff (C := C) z hres i c).mp
    (localCohomologyScalarEndomorphism_eq_zero_of_tor_annihilated z hres C I hTor i hi c hc)
  rw [Module.mem_annihilator]
  intro x
  exact congrArg (fun f => f.hom x) h

end SerrePositivity
