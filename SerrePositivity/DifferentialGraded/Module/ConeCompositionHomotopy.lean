module
public import SerrePositivity.DifferentialGraded.Module.ConeCompositionDesc
public import SerrePositivity.DifferentialGraded.Module.Homotopy

/-! # 合成cone比較の全dg自然な収縮とK(D)の同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleConeCompContractingLeft {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).X (-2) :=
  compose A (x := ForgetEnrichment.to (Complex A) M)
    (y := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (moduleConeInlElement A D (moduleConeCompMap A D f g)) (moduleConeInlElement A D f)
    (show (-1 : ℤ) + (-1) = -2 by decide)

def moduleConeCompContractingMiddle {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).X (-1) :=
  compose A (x := ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))
    (y := ForgetEnrichment.to (Complex A) M)
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (moduleConeCompContractingLeft A D f g) (moduleConeFstElement A D (f ≫ g))
    (show (1 : ℤ) + (-2) = -1 by decide)

def moduleConeCompContractingElement {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).X (-1) :=
  -compose A
    (x := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (y := ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))
    (z := ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
    (moduleConeCompContractingMiddle A D f g)
    (moduleConeSndElement A D (moduleConeCompMap A D f g)) (zero_add (-1))

lemma moduleConeCompContractingElement_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g))) x).f (-1)
        (moduleConeCompContractingElement A D f g) =
      -((mappingCone.snd ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))).comp
        ((mappingCone.fst ((moduleEvaluation A D x).map (f ≫ g))).val.comp
          ((mappingCone.inl ((moduleEvaluation A D x).map f)).comp
            (mappingCone.inl ((moduleEvaluation A D x).map (moduleConeCompMap A D f g)))
            (show (-1 : ℤ) + (-1) = -2 by decide))
          (show (1 : ℤ) + (-2) = -1 by decide)) (zero_add (-1))) := by
  rw [moduleConeCompContractingElement, map_neg, moduleHomCompose_π,
    moduleConeCompContractingMiddle, moduleHomCompose_π,
    moduleConeCompContractingLeft, moduleHomCompose_π,
    moduleConeSndElement_π, moduleConeFstElement_π, moduleConeInlElement_π, moduleConeInlElement_π]

lemma moduleConeCompContractingElement_d {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (moduleConeCompMap A D f g)))).d (-1) 0
        (moduleConeCompContractingElement A D f g) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (moduleConeCompInv A D f g ≫ moduleConeCompHom A D f g))).val -
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (𝟙 (moduleCone A D (moduleConeCompMap A D f g))))).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompContractingElement_π, map_sub,
    ← moduleEvaluation_cochain, ← moduleEvaluation_cochain,
    (moduleEvaluation A D x).map_comp (moduleConeCompInv A D f g) (moduleConeCompHom A D f g),
    moduleConeCompInv_eval, moduleConeCompHom_eval, CategoryTheory.Functor.map_id]
  exact complexConeComp_inv_hom_boundary _ _ _ _ _ _

/-- 逆順の比較射の合成を恒等射へ収縮する全dg自然なホモトピー。 -/
def moduleConeCompInvHomHomotopy {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    ModuleHomotopy A D (moduleConeCompInv A D f g ≫ moduleConeCompHom A D f g) (𝟙 _) :=
  ⟨moduleConeCompContractingElement A D f g, moduleConeCompContractingElement_d A D f g⟩

/-- cone(g)とcone(cone(f)→cone(f≫g))はK(D)で同型。 -/
def moduleConeCompHomotopyIso {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleToHomotopy A D).obj (moduleCone A D g) ≅
      (moduleToHomotopy A D).obj (moduleCone A D (moduleConeCompMap A D f g)) where
  hom := (moduleToHomotopy A D).map (moduleConeCompHom A D f g)
  inv := (moduleToHomotopy A D).map (moduleConeCompInv A D f g)
  hom_inv_id := by
    rw [← CategoryTheory.Functor.map_comp, moduleConeComp_hom_inv, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    rw [← CategoryTheory.Functor.map_comp]
    exact ((moduleToHomotopy_map_eq_iff A D _ _).2
      ⟨moduleConeCompInvHomHomotopy A D f g⟩).trans ((moduleToHomotopy A D).map_id _)

end SerrePositivity.DifferentialGraded
