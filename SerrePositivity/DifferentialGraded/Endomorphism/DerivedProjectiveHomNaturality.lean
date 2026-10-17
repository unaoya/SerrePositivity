module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedHomEquiv
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting

/-! # 射影的始域での再構成Hom同値の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

lemma endomorphismHomotopyHomEquiv_map
    (P : ModuleCategory A (EndomorphismObject E)) (M : ModuleCategory A D)
    (s : (endomorphismModuleTensor A D E).onClosed.obj P ⟶ M) :
    (endomorphismHomotopyAdjunction A D E).homEquiv
        ((moduleToHomotopy A (EndomorphismObject E)).obj P) ((moduleToHomotopy A D).obj M)
        ((moduleToHomotopy A D).map s) =
      (moduleToHomotopy A (EndomorphismObject E)).map
        ((endomorphismModuleAdjunction A D E).homEquiv P M s) := by
  rw [Adjunction.homEquiv_unit]
  change (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleUnit A D E).app P) ≫
    (moduleToHomotopy A (EndomorphismObject E)).map
      ((endomorphismModuleHom A D E).onClosed.map s) = _
  rw [← Functor.map_comp]
  exact congrArg (moduleToHomotopy A (EndomorphismObject E)).map
    ((endomorphismModuleAdjunction A D E).homEquiv_unit P M s).symm

variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismProjectiveDerivedHomEquiv_map
    (P : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P)
    (M : ModuleCategory A D)
    (s : (endomorphismModuleTensor A D E).onClosed.obj P ⟶ M) :
    endomorphismProjectiveDerivedHomEquiv A D E hE P hP M ((moduleToDerived A D).map s) =
      (moduleToDerived A (EndomorphismObject E)).map
          ((endomorphismModuleAdjunction A D E).homEquiv P M s) ≫
        (endomorphismDerivedHomComputation A D E hE M).inv := by
  have hs := moduleProjectiveDerivedHomEquiv_map A D
    (endomorphismModuleTensor_homotopicallyProjective A D E hE hP) s
  unfold endomorphismProjectiveDerivedHomEquiv
  simp only [Equiv.trans_apply]
  rw [← hs, Equiv.symm_apply_apply]
  have ht := endomorphismHomotopyHomEquiv_map A D E P M s
  have hu := congrArg
    (moduleProjectiveDerivedHomEquiv A (EndomorphismObject E) hP
      ((endomorphismModuleHom A D E).onClosed.obj M)) ht
  have hv := hu.trans (moduleProjectiveDerivedHomEquiv_map A (EndomorphismObject E) hP
    ((endomorphismModuleAdjunction A D E).homEquiv P M s))
  exact (congrArg
    (Iso.homCongr (Iso.refl _) (endomorphismDerivedHomComputation A D E hE M).symm) hv).trans
      (by simp [Iso.homCongr])

lemma endomorphismDerivedHomComputation_inv_naturality
    {M M' : ModuleCategory A D} (f : M ⟶ M') :
    (moduleToDerived A (EndomorphismObject E)).map
        ((endomorphismModuleHom A D E).onClosed.map f) ≫
        (endomorphismDerivedHomComputation A D E hE M').inv =
      (endomorphismDerivedHomComputation A D E hE M).inv ≫
        (endomorphismDerivedHom A D E hE).map ((moduleToDerived A D).map f) := by
  exact (eqToIso (endomorphismDerivedHom_fac A D E hE)).inv.naturality f

lemma endomorphismProjectiveDerivedHomEquiv_naturality_right
    (P : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P)
    {M M' : ModuleCategory A D}
    (φ : (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj P) ⟶
      (moduleToDerived A D).obj M) (f : M ⟶ M') :
    endomorphismProjectiveDerivedHomEquiv A D E hE P hP M'
        (φ ≫ (moduleToDerived A D).map f) =
      endomorphismProjectiveDerivedHomEquiv A D E hE P hP M φ ≫
        (endomorphismDerivedHom A D E hE).map ((moduleToDerived A D).map f) := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A D
    (endomorphismModuleTensor_homotopicallyProjective A D E hE hP) φ
  rw [← Functor.map_comp, endomorphismProjectiveDerivedHomEquiv_map,
    endomorphismProjectiveDerivedHomEquiv_map,
    Adjunction.homEquiv_naturality_right, Functor.map_comp, Category.assoc,
    endomorphismDerivedHomComputation_inv_naturality, Category.assoc]

lemma endomorphismProjectiveDerivedHomEquiv_naturality_left
    (P Q : ModuleCategory A (EndomorphismObject E))
    (hP : moduleHomotopicallyProjective A (EndomorphismObject E) P)
    (hQ : moduleHomotopicallyProjective A (EndomorphismObject E) Q)
    (M : ModuleCategory A D) (f : P ⟶ Q)
    (φ : (moduleToDerived A D).obj ((endomorphismModuleTensor A D E).onClosed.obj Q) ⟶
      (moduleToDerived A D).obj M) :
    endomorphismProjectiveDerivedHomEquiv A D E hE P hP M
        ((moduleToDerived A D).map ((endomorphismModuleTensor A D E).onClosed.map f) ≫ φ) =
      (moduleToDerived A (EndomorphismObject E)).map f ≫
        endomorphismProjectiveDerivedHomEquiv A D E hE Q hQ M φ := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A D
    (endomorphismModuleTensor_homotopicallyProjective A D E hE hQ) φ
  rw [← Functor.map_comp, endomorphismProjectiveDerivedHomEquiv_map,
    endomorphismProjectiveDerivedHomEquiv_map,
    Adjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
