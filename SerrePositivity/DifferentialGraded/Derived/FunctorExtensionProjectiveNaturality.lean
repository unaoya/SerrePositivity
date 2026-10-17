module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionHom
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveDerivedLifting

/-! # 射影的始域でのgraph導来延長Hom同値の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgProjectiveDerivedExtensionHomEquiv_map (P : ModuleCategory A D)
    (hP : moduleHomotopicallyProjective A D P) (M : ModuleCategory A E)
    (s : (dgModuleExtension A D E F).onClosed.obj P ⟶ M) :
    dgProjectiveDerivedExtensionHomEquiv A D E F P hP M ((moduleToDerived A E).map s) =
      (moduleToDerived A D).map
          ((dgModuleEnrichedRestrictionAdjunction A D E F).homEquiv P M s) ≫
        (dgDerivedRestrictionComputation A D E F M).inv := by
  have hs := moduleProjectiveDerivedHomEquiv_map A E
    (dgModuleExtension_homotopicallyProjective A D E F hP) s
  unfold dgProjectiveDerivedExtensionHomEquiv
  simp only [Equiv.trans_apply]
  rw [← hs, Equiv.symm_apply_apply]
  have ht := DGFunctor.homotopyAdjunction_homEquiv_map
    (dgModuleExtension A D E F) (dgModuleRestriction A D E F.op)
    (dgModuleEnrichedRestrictionAdjunction A D E F) P M s
  have hu := congrArg (moduleProjectiveDerivedHomEquiv A D hP
    ((dgModuleRestriction A D E F.op).onClosed.obj M)) ht
  have hv := hu.trans (moduleProjectiveDerivedHomEquiv_map A D hP
    ((dgModuleEnrichedRestrictionAdjunction A D E F).homEquiv P M s))
  exact (congrArg (Iso.homCongr (Iso.refl _)
    (dgDerivedRestrictionComputation A D E F M).symm) hv).trans (by simp [Iso.homCongr])

lemma dgDerivedRestrictionComputation_inv_naturality {M M' : ModuleCategory A E} (f : M ⟶ M') :
    (moduleToDerived A D).map ((dgModuleRestriction A D E F.op).onClosed.map f) ≫
        (dgDerivedRestrictionComputation A D E F M').inv =
      (dgDerivedRestrictionComputation A D E F M).inv ≫
        (dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f) := by
  have h := (eqToIso (dgDerivedRestriction_fac A D E F)).inv.naturality f
  rw [dgModuleRestriction_map]
  exact h

lemma dgProjectiveDerivedExtensionHomEquiv_naturality_right
    (P : ModuleCategory A D) (hP : moduleHomotopicallyProjective A D P)
    {M M' : ModuleCategory A E}
    (φ : (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj P) ⟶
      (moduleToDerived A E).obj M) (f : M ⟶ M') :
    dgProjectiveDerivedExtensionHomEquiv A D E F P hP M'
        (φ ≫ (moduleToDerived A E).map f) =
      dgProjectiveDerivedExtensionHomEquiv A D E F P hP M φ ≫
        (dgDerivedRestriction A D E F).map ((moduleToDerived A E).map f) := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A E
    (dgModuleExtension_homotopicallyProjective A D E F hP) φ
  rw [← Functor.map_comp, dgProjectiveDerivedExtensionHomEquiv_map,
    dgProjectiveDerivedExtensionHomEquiv_map, Adjunction.homEquiv_naturality_right,
    Functor.map_comp, Category.assoc, dgDerivedRestrictionComputation_inv_naturality,
    Category.assoc]

lemma dgProjectiveDerivedExtensionHomEquiv_naturality_left
    (P Q : ModuleCategory A D) (hP : moduleHomotopicallyProjective A D P)
    (hQ : moduleHomotopicallyProjective A D Q) (M : ModuleCategory A E) (f : P ⟶ Q)
    (φ : (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj Q) ⟶
      (moduleToDerived A E).obj M) :
    dgProjectiveDerivedExtensionHomEquiv A D E F P hP M
        ((moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) ≫ φ) =
      (moduleToDerived A D).map f ≫ dgProjectiveDerivedExtensionHomEquiv A D E F Q hQ M φ := by
  obtain ⟨s, rfl⟩ := moduleProjectiveToDerived_map_surjective A E
    (dgModuleExtension_homotopicallyProjective A D E F hQ) φ
  rw [← Functor.map_comp, dgProjectiveDerivedExtensionHomEquiv_map,
    dgProjectiveDerivedExtensionHomEquiv_map, Adjunction.homEquiv_naturality_left,
    Functor.map_comp, Category.assoc]

end SerrePositivity.DifferentialGraded
