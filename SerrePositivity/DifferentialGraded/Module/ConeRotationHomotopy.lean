module
public import SerrePositivity.DifferentialGraded.Module.ConeRotation

/-! # 回転比較の全dg自然な収縮とK(D)の同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeRotationConnectingElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).X (-1) :=
  -compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (y := ForgetEnrichment.to (Complex A) N)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
    (moduleConeInlElement A D (moduleConeInr A D f)) (moduleConeSndElement A D f) (by omega)

def moduleConeRotationContractingElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
    (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
    (moduleConeRotationConnectingElement A D f)
    (moduleConeSndElement A D (moduleConeInr A D f)) (by omega)

lemma moduleConeRotationConnectingElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f))) x).f (-1)
        (moduleConeRotationConnectingElement A D f) =
      -(mappingCone.snd ((moduleEvaluation A D x).map f)).comp
        (mappingCone.inl ((moduleEvaluation A D x).map (moduleConeInr A D f))) (zero_add (-1)) := by
  rw [moduleConeRotationConnectingElement, map_neg, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeInlElement_π]

lemma moduleConeRotationContractingElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f))) x).f (-1)
        (moduleConeRotationContractingElement A D f) =
      -(mappingCone.snd ((moduleEvaluation A D x).map (moduleConeInr A D f))).comp
        ((mappingCone.snd ((moduleEvaluation A D x).map f)).comp
          (mappingCone.inl ((moduleEvaluation A D x).map (moduleConeInr A D f))) (zero_add (-1)))
        (zero_add (-1)) := by
  rw [moduleConeRotationContractingElement, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeRotationConnectingElement_π, Cochain.comp_neg]

lemma moduleConeRotationContractingElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).d (-1) 0
        (moduleConeRotationContractingElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeRotationInv A D f ≫ moduleConeRotationHom A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (𝟙 (moduleCone A D (moduleConeInr A D f))))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeRotationContractingElement_π, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain, CategoryTheory.Functor.map_comp,
    moduleConeRotationInv_eval, moduleConeRotationHom_eval, CategoryTheory.Functor.map_id]
  exact complexConeRotation_inv_hom_boundary _ _ _

def moduleConeRotationInvHomHomotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleHomotopy A D (moduleConeRotationInv A D f ≫ moduleConeRotationHom A D f) (𝟙 _) :=
  ⟨moduleConeRotationContractingElement A D f, moduleConeRotationContractingElement_d A D f⟩

lemma moduleConeRotationConnectingElement_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeInr A D f)))).d (-1) 0
        (moduleConeRotationConnectingElement A D f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeConnecting A D f ≫ moduleConeRotationHom A D f))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeInr A D (moduleConeInr A D f)))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeRotationConnectingElement_π, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain, CategoryTheory.Functor.map_comp,
    moduleConeConnecting_eval, moduleConeRotationHom_eval,
    moduleConeInr_eval A D (moduleConeInr A D f) x]
  exact complexConeRotation_connecting_boundary _ _ _

def moduleConeRotationConnectingHomotopy {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleHomotopy A D (moduleConeConnecting A D f ≫ moduleConeRotationHom A D f)
      (moduleConeInr A D (moduleConeInr A D f)) :=
  ⟨moduleConeRotationConnectingElement A D f, moduleConeRotationConnectingElement_d A D f⟩

lemma moduleConeRotation_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeRotationHom A D f ≫ moduleConeConnecting A D (moduleConeInr A D f) =
      -f⟦(1 : ℤ)⟧' := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeRotationHom_eval,
    moduleConeConnecting_eval, CategoryTheory.Functor.map_neg]
  have hs : (moduleEvaluation A D x).map (f⟦(1 : ℤ)⟧') =
      ((moduleEvaluation A D x).map f)⟦(1 : ℤ)⟧' :=
    moduleShiftFunctor_map_eval A D 1 f x
  rw [hs]
  exact complexConeRotation_connecting _ _ _

/-- 回転比較の第三対象の同型。 -/
def moduleConeRotationHomotopyIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleToHomotopy A D).obj (moduleShiftObj A D 1 M) ≅
      (moduleToHomotopy A D).obj (moduleCone A D (moduleConeInr A D f)) where
  hom := (moduleToHomotopy A D).map (moduleConeRotationHom A D f)
  inv := (moduleToHomotopy A D).map (moduleConeRotationInv A D f)
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp, moduleConeRotation_hom_inv,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2
      ⟨moduleConeRotationInvHomHomotopy A D f⟩).trans ((moduleToHomotopy A D).map_id _)


/-- 商関手のshift比較を含めた、回転三角形の第三対象の同型。 -/
def moduleConeRotationShiftIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    ((moduleToHomotopy A D).obj M)⟦(1 : ℤ)⟧ ≅
      (moduleToHomotopy A D).obj (moduleCone A D (moduleConeInr A D f)) :=
  ((moduleToHomotopy A D).commShiftIso (1 : ℤ)).symm.app M ≪≫
    moduleConeRotationHomotopyIso A D f

end SerrePositivity.DifferentialGraded
