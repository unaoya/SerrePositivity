module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomShift
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleShiftImage

/-! # 実際の加群係数拡大と整数shiftの比較同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D)) (Complex A'))

def scalarModuleShiftImageOut (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj (shiftModule s M)) (F.obj M) s :=
  let := φ.toAlgebra
  (F.map (shiftModule s M) M).f s ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)

def scalarModuleShiftImageIn (s : ℤ) (M : RightModule A D) :
    Cochain (F.obj M) (F.obj (shiftModule s M)) (-s) :=
  let := φ.toAlgebra
  (F.map M (shiftModule s M)).f (-s) ((1 : A') ⊗ₜ[A] moduleShiftInElement A D s M)

lemma scalarModuleShiftImageOut_d (s : ℤ) (M : RightModule A D) :
    δ s (s + 1) (scalarModuleShiftImageOut φ D F s M) = 0 := by
  let := φ.toAlgebra
  have h := F.map_d_cochain A' (x := shiftModule s M) (y := M)
    ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M) (q := s + 1)
  have hz : (F.map (shiftModule s M) M).f (s + 1)
      ((ModuleCat.extendScalars φ).map ((moduleHom A D (shiftModule s M) M).d s (s + 1))
        ((1 : A') ⊗ₜ[A] moduleShiftOutElement A D s M)) = 0 := by
    erw [ModuleCat.ExtendScalars.map_tmul φ]
    rw [moduleShiftOutElement_d, TensorProduct.tmul_zero, map_zero]
  exact h.symm.trans hz

lemma scalarModuleShiftImageOutIn (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftImageOut φ D F s M).comp (scalarModuleShiftImageIn φ D F s M)
      (add_neg_cancel s) = Cochain.ofHom (𝟙 (F.obj (shiftModule s M))) := by
  let := φ.toAlgebra
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := shiftModule s M) (y := M) (z := shiftModule s M)
    (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M) (add_neg_cancel s)
  have he := congrArg (fun z : GradedHom A (shiftModule s M) (shiftModule s M) 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftOutIn A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) (shiftModule s M)
  have h := congrArg (fun z => (F.map (shiftModule s M) (shiftModule s M)).f 0 z)
    (hc.trans (he.trans hu.symm))
  rw [DGFunctor.map_compose_cochain, F.map_unitElement A', Bimodule.complex_unitElement] at h
  exact h

lemma scalarModuleShiftImageInOut (s : ℤ) (M : RightModule A D) :
    (scalarModuleShiftImageIn φ D F s M).comp (scalarModuleShiftImageOut φ D F s M)
      (neg_add_cancel s) = Cochain.ofHom (𝟙 (F.obj M)) := by
  let := φ.toAlgebra
  have hc := scalarBaseChange_compose φ (D := RightModule A D)
    (x := M) (y := shiftModule s M) (z := M)
    (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M) (neg_add_cancel s)
  have he := congrArg (fun z : GradedHom A M M 0 =>
    (1 : A') ⊗ₜ[A] z) (moduleShiftInOut A D s M)
  have hu := scalarUnitElement_one φ (RightModule A D) M
  have h := congrArg (fun z => (F.map M M).f 0 z) (hc.trans (he.trans hu.symm))
  rw [DGFunctor.map_compose_cochain, F.map_unitElement A', Bimodule.complex_unitElement] at h
  exact h

def scalarModuleShiftImageIso (s : ℤ) (M : RightModule A D) :
    F.obj (shiftModule s M) ≅ (F.obj M)⟦s⟧ :=
  complexShiftIso A' (scalarModuleShiftImageOut φ D F s M)
    (scalarModuleShiftImageOut_d φ D F s M) (scalarModuleShiftImageIn φ D F s M)
    (scalarModuleShiftImageOutIn φ D F s M) (scalarModuleShiftImageInOut φ D F s M)

omit F in
lemma scalarModuleExtensionShift_naturality (s : ℤ) (M : RightModule A D) :
    ∀ x y, (ScalarExtension.rightModule φ D (shiftModule s M)).map x y ≫
        homPostcompose ((ScalarExtension.rightModule φ D (shiftModule s M)).obj x)
          (scalarModuleShiftImageIso φ D
            ((scalarModuleDGFunctor φ D).comp
              (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) y.unop)) s M).hom =
      (shiftModule s (ScalarExtension.rightModule φ D M)).map x y ≫
        homPrecompose
          (scalarModuleShiftImageIso φ D ((scalarModuleDGFunctor φ D).comp
            (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x.unop)) s M).hom
          ((shiftModule s (ScalarExtension.rightModule φ D M)).obj y) := by
  apply moduleShiftRepresentation_naturality A' (ScalarExtension.DGBaseChange φ D) s
    (scalarModuleHomElement φ D (moduleShiftOutElement A D s M))
  intro x i
  change (complexShiftComparison A' _ _).f i = _
  rw [complexShiftComparison_f]
  rfl

omit F in
/-- 全次数自然な加群同型としての、実際の係数拡大と整数shiftの比較。 -/
def scalarModuleExtensionShiftIso (s : ℤ) (M : RightModule A D) :
    (ScalarExtension.moduleExtension φ D).obj
        (ForgetEnrichment.of (Complex A) (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A') (shiftModule s (ScalarExtension.rightModule φ D M)) :=
  moduleIsoMk A' (ScalarExtension.DGBaseChange φ D)
    (fun x => scalarModuleShiftImageIso φ D ((scalarModuleDGFunctor φ D).comp
      (moduleEvaluationDG A' (ScalarExtension.DGBaseChange φ D) x.unop)) s M)
    (scalarModuleExtensionShift_naturality φ D s M)

end SerrePositivity.DifferentialGraded
