module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Category.HomotopyHomologyLinear
public import SerrePositivity.DifferentialGraded.Derived.Linear

/-! # 射影的始域・代表加群の導来Hom計算のA線形性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleProjectiveDerivedHomEquiv_add {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D)
    (f g : (moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) :
    moduleProjectiveDerivedHomEquiv A D hP N (f + g) =
      moduleProjectiveDerivedHomEquiv A D hP N f + moduleProjectiveDerivedHomEquiv A D hP N g := by
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  rw [← (moduleToHomotopy A D).map_add, moduleProjectiveDerivedHomEquiv_map,
    moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
    (moduleToDerived A D).map_add]

lemma moduleProjectiveDerivedHomEquiv_smul {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) (a : A)
    (f : (moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) :
    moduleProjectiveDerivedHomEquiv A D hP N (a • f) =
      a • moduleProjectiveDerivedHomEquiv A D hP N f := by
  obtain ⟨f, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  rw [← (moduleToHomotopy A D).map_smul, moduleProjectiveDerivedHomEquiv_map,
    moduleProjectiveDerivedHomEquiv_map, (moduleToDerived A D).map_smul]

def moduleProjectiveDerivedHomLinearEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) ≃ₗ[A]
      ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) where
  __ := moduleProjectiveDerivedHomEquiv A D hP N
  map_add' := moduleProjectiveDerivedHomEquiv_add A D hP N
  map_smul' := moduleProjectiveDerivedHomEquiv_smul A D hP N

def moduleProjectiveDerivedHomologyLinearEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) ≃ₗ[A]
      (moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) N)).homology 0 :=
  (moduleProjectiveDerivedHomLinearEquiv A D hP N).symm.trans
    (homotopyHomologyLinearEquiv A (RightModule A D) P N)

def moduleRepresentableDerivedHomologyLinearEquiv (x : D) (N : ModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶
      (moduleToDerived A D).obj N) ≃ₗ[A]
        ((ForgetEnrichment.to (Complex A) N).obj (op x)).homology 0 :=
  (moduleProjectiveDerivedHomologyLinearEquiv A D
    (representable_homotopicallyProjective A D x) N).trans
    (HomologicalComplex.homologyMapIso
      (dgYonedaIso A x (ForgetEnrichment.to (Complex A) N)) 0).toLinearEquiv

def moduleRepresentableDerivedHomLinearEquiv (x : D) (X : DerivedModuleCategory A D) :
    ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A x)) ⟶ X) ≃ₗ[A]
      (moduleDerivedHomology A D x 0).obj X := by
  obtain ⟨⟨N⟩⟩ := X
  exact moduleRepresentableDerivedHomologyLinearEquiv A D x N

lemma moduleRepresentableDerivedHomLinearEquiv_toEquiv (x : D) (X : DerivedModuleCategory A D) :
    (moduleRepresentableDerivedHomLinearEquiv A D x X).toEquiv =
      moduleRepresentableDerivedHomEquiv A D x X := by
  obtain ⟨⟨N⟩⟩ := X
  rfl

end SerrePositivity.DifferentialGraded
