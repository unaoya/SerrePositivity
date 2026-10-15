module
public import SerrePositivity.DifferentialGraded.Module.ConeLift
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc
public import SerrePositivity.DifferentialGraded.Module.ConeFunctor
public import SerrePositivity.DifferentialGraded.Complexes.ConeComposition

/-! # 合成coneの比較射に用いる全dg自然な入力 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 合成f≫gによる標準cone射cone(f)→cone(f≫g)。 -/
def moduleConeCompMap {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D f ⟶ moduleCone A D (f ≫ g) :=
  moduleConeMap A D f (f ≫ g) (𝟙 M) g (by simp)

lemma moduleConeCompMap_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompMap A D f g) =
      mappingCone.map ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map (f ≫ g))
        (𝟙 ((moduleEvaluation A D x).obj M)) ((moduleEvaluation A D x).map g)
        (by rw [CategoryTheory.Functor.map_comp, Category.id_comp]) := by
  unfold moduleConeCompMap
  simpa only [CategoryTheory.Functor.map_id] using
    moduleConeMap_eval A D f (f ≫ g) (𝟙 M) g (by simp) x

/-- cone(g)→cone(f)の次数1の入力。 -/
def moduleConeCompLiftFirst {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).X 1 :=
  (eHomWhiskerLeft (Complex A) (moduleCone A D g) (moduleConeInr A D f)).f 1
    (moduleConeFstElement A D g)

/-- cone(g)→cone(f≫g)の次数0の入力。閉性は二つの入力を組み合わせて得る。 -/
def moduleConeCompLiftSecond {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))).X 0 :=
  moduleConeDescElement A D g 0 (moduleConeInr A D (f ≫ g))

lemma moduleConeCompLiftFirst_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 1
        (moduleConeCompLiftFirst A D f g) =
      (mappingCone.fst ((moduleEvaluation A D x).map g)).val.comp
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map f))) (add_zero 1) := by
  rw [moduleConeCompLiftFirst, moduleHomWhiskerLeft_apply_π,
    moduleConeFstElement_π, moduleConeInr_eval]

lemma moduleConeCompLiftSecond_π {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g))) x).f 0
        (moduleConeCompLiftSecond A D f g) =
      mappingCone.descCochain ((moduleEvaluation A D x).map g) 0
        (Cochain.ofHom (mappingCone.inr ((moduleEvaluation A D x).map (f ≫ g))))
        (neg_add_cancel 1) := by
  rw [moduleConeCompLiftSecond, moduleConeDescElement_π, map_zero, moduleConeInr_eval]

lemma moduleConeCompLiftFirst_closed {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d 1 2
        (moduleConeCompLiftFirst A D f g) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleConeCompLiftFirst_π, map_zero]
  simp only [δ_comp_ofHom, Cocycle.δ_eq_zero, Cochain.zero_comp]

lemma moduleConeCompLiftInputs_cycle {M N P : ModuleCategory A D}
    (f : M ⟶ N) (g : N ⟶ P) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))).d 0 1
        (moduleConeCompLiftSecond A D f g) +
      (show (moduleHom A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
        (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g)))).X 1 from
          (eHomWhiskerLeft (Complex A) (moduleCone A D g) (moduleConeCompMap A D f g)).f 1
            (moduleConeCompLiftFirst A D f g)) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomElement_d_π, moduleConeCompLiftSecond_π,
    moduleHomWhiskerLeft_apply_π, moduleConeCompLiftFirst_π, map_zero]
  exact complexConeComp_inputs_cycle ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)
    ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
    (moduleConeCompMap_eval A D f g x)

/-- 全dg自然なcone(g)→cone(cone(f)→cone(f≫g))の順方向比較射。 -/
def moduleConeCompHom {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D g ⟶ moduleCone A D (moduleConeCompMap A D f g) :=
  moduleConeLiftOfCycle A D (moduleConeCompMap A D f g)
    (moduleConeCompLiftFirst A D f g) (moduleConeCompLiftSecond A D f g)
    (moduleConeCompLiftFirst_closed A D f g) (moduleConeCompLiftInputs_cycle A D f g)

@[simp] lemma moduleConeCompHom_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompHom A D f g) =
      (complexConeCompHomotopyEquiv ((moduleEvaluation A D x).map f)
        ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
        ((moduleEvaluation A D x).map_comp f g)
        ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
        (moduleConeCompMap_eval A D f g x)).hom := by
  unfold moduleConeCompHom
  rw [moduleConeLiftOfCycle_eval]
  apply Cochain.ofHom_injective
  rw [mappingCone.ofHom_lift, complexConeComp_hom_cochain]
  change mappingCone.liftCochain ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)) x).f 1
        (moduleConeCompLiftFirst A D f g))
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) (moduleCone A D g))
      (ForgetEnrichment.to (Complex A) (moduleCone A D (f ≫ g))) x).f 0
        (moduleConeCompLiftSecond A D f g)) (zero_add 1) = _
  rw [moduleConeCompLiftFirst_π, moduleConeCompLiftSecond_π]

end SerrePositivity.DifferentialGraded
