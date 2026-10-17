module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLengthModule
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedModule
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-! # 長さ filtration の層射影を右 dg 加群射にする -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 層射影は、最終微分についての先頭作用を固定長の内部作用へ移す。 -/
lemma lengthLayerProjection_prepend (S : Set D) (x y z : D) (n : ℕ) :
    lengthPrepend A D S x y z (n + 1) ≫ lengthLayerProjection A D S x z n =
      (homObject A D x y ◁ lengthLayerProjection A D S y z n) ≫
        selectedPrepend A D S (fun w => w.length = n + 1) x y z := by
  apply tensorHom_ext
  intro p q r hr
  rw [HomologicalComplex.comp_f, ← Category.assoc, lengthPrepend_ι,
    HomologicalComplex.comp_f, ← Category.assoc, ι_whiskerLeft]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f t
  change (fixedLengthProjection A D S x z (n + 1)).f r
      (lengthPrependComponent A D S x y z (n + 1) p q r hr (f ⊗ₜ[A] t)).val =
    (selectedPrepend A D S (fun w => w.length = n + 1) x y z).f r
      (ιTensorObj (homObject A D x y) (fixedLengthHom A D S y z (n + 1)) p q r hr
        (f ⊗ₜ[A] (fixedLengthProjection A D S y z (n + 1)).f q t.val))
  rw [lengthPrependComponent_coe]
  have h := congrArg (fun g => g.f r
    (ιTensorObj (homObject A D x y) (internalHom A D S y z) p q r hr (f ⊗ₜ[A] t.val)))
      (selectedProjection_prepend A D S (fun w => w.length = n + 1) x y z)
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at h
  rw [whiskerLeft_apply] at h
  exact h

/-- 固定長 path 加群へ値を移した層射影。 -/
def lengthLayerModuleComponent (S : Set D) (z : D) (n : ℕ) (x : Dᵒᵖ) :
    lengthComplex A D S x.unop z (n + 1) ⟶
      (moduleEvaluation A D x.unop).obj
        (selectedPathModule A D S (fun w => w.length = n + 1) z) :=
  lengthLayerProjection A D S x.unop z n ≫
    (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z x).inv

@[reassoc] lemma lengthLayerModuleComponent_evaluation (S : Set D) (z : D) (n : ℕ)
    (x : Dᵒᵖ) :
    lengthLayerModuleComponent A D S z n x ≫
        (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z x).hom =
      lengthLayerProjection A D S x.unop z n := by
  dsimp only [lengthLayerModuleComponent]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma lengthLayerModuleComponent_action (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ) :
    moduleActionChain A (lengthModule A D S z (n + 1)) x y ≫
        lengthLayerModuleComponent A D S z n y =
      ((x ⟶[Complex A] y) ◁ lengthLayerModuleComponent A D S z n x) ≫
        moduleActionChain A (ForgetEnrichment.to (Complex A)
          (selectedPathModule A D S (fun w => w.length = n + 1) z)) x y := by
  apply (cancel_mono
    (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z y).hom).mp
  calc
    _ = lengthPrepend A D S y.unop x.unop z (n + 1) ≫
        lengthLayerProjection A D S y.unop z n := by
      rw [Category.assoc, lengthLayerModuleComponent_evaluation]
      change uncurryRight (curryRight (lengthPrepend A D S y.unop x.unop z (n + 1))) ≫ _ = _
      rw [uncurryRight_curryRight]
    _ = ((x ⟶[Complex A] y) ◁ lengthLayerProjection A D S x.unop z n) ≫
        selectedPrepend A D S (fun w => w.length = n + 1) y.unop x.unop z :=
      lengthLayerProjection_prepend A D S y.unop x.unop z n
    _ = _ := by
      have h := congrArg (fun f =>
        ((x ⟶[Complex A] y) ◁ lengthLayerModuleComponent A D S z n x) ≫ f)
          (selectedPathModuleEvaluationIso_action A D S (fun w => w.length = n + 1) z x y)
      simp only [← Category.assoc] at h
      rw [← MonoidalCategory.whiskerLeft_comp, lengthLayerModuleComponent_evaluation] at h
      exact h.symm

lemma lengthLayerModuleComponent_naturality (S : Set D) (z : D) (n : ℕ) (x y : Dᵒᵖ) :
    (lengthModule A D S z (n + 1)).map x y ≫
        homPostcompose (lengthComplex A D S x.unop z (n + 1))
          (lengthLayerModuleComponent A D S z n y) =
      (ForgetEnrichment.to (Complex A)
        (selectedPathModule A D S (fun w => w.length = n + 1) z)).map x y ≫
          homPrecompose (lengthLayerModuleComponent A D S z n x)
            ((moduleEvaluation A D y.unop).obj
              (selectedPathModule A D S (fun w => w.length = n + 1) z)) := by
  have h := congrArg curryRight (lengthLayerModuleComponent_action A D S z n x y)
  change curryRight (uncurryRight ((lengthModule A D S z (n + 1)).map x y) ≫
    lengthLayerModuleComponent A D S z n y) =
      curryRight ((𝟙 (x ⟶[Complex A] y) ⊗ₘ lengthLayerModuleComponent A D S z n x) ≫
        uncurryRight ((ForgetEnrichment.to (Complex A)
          (selectedPathModule A D S (fun w => w.length = n + 1) z)).map x y)) at h
  rw [curryRight_naturality_target, curryRight_naturality_domain,
    curryRight_uncurryRight, curryRight_uncurryRight] at h
  exact h

/-- 固定長部分への実際の全次数自然な右 dg 加群射。 -/
def lengthLayerModuleProjection (S : Set D) (z : D) (n : ℕ) :
    ForgetEnrichment.of (Complex A) (lengthModule A D S z (n + 1)) ⟶
      selectedPathModule A D S (fun w => w.length = n + 1) z :=
  moduleMorphismMk A D (lengthLayerModuleComponent A D S z n)
    (lengthLayerModuleComponent_naturality A D S z n)

@[simp] lemma lengthLayerModuleProjection_eval (S : Set D) (z : D) (n : ℕ) (x : D) :
    (moduleEvaluation A D x).map (lengthLayerModuleProjection A D S z n) =
      lengthLayerProjection A D S x z n ≫
        (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z (op x)).inv :=
  moduleMorphismMk_eval A D _ _ x

lemma lengthModuleTransition_layerProjection (S : Set D) (z : D) (n : ℕ) :
    lengthModuleTransition A D S z (Nat.le_succ n) ≫ lengthLayerModuleProjection A D S z n = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, lengthModuleTransition_eval,
    lengthLayerModuleProjection_eval, CategoryTheory.Functor.map_zero,
    ← Category.assoc, lengthMap_layerProjection, zero_comp]

/-- 固定長加群は、相隣る長さ部分加群の包含の真の cokernel。 -/
def lengthLayerModule_isColimit (S : Set D) (z : D) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (lengthLayerModuleProjection A D S z n)
      (lengthModuleTransition_layerProjection A D S z n)) := by
  apply moduleIsColimitOfEvaluations A D
  intro x
  refine (isColimitMapCoconeCoforkEquiv' (moduleEvaluation A D x)
    (lengthModuleTransition_layerProjection A D S z n)).symm ?_
  refine Cofork.isColimitOfIsos _ (lengthLayer_isColimit A D S x z n) _
    (Iso.refl _) (Iso.refl _) (selectedPathModuleEvaluationIso A D S
      (fun w => w.length = n + 1) z (op x)).symm ?_ ?_ ?_
  · change 𝟙 _ ≫ (moduleEvaluation A D x).map
        (lengthModuleTransition A D S z (Nat.le_succ n)) =
      lengthMap A D S x z (Nat.le_succ n) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, lengthModuleTransition_eval]
  · simp
  · change 𝟙 _ ≫ lengthLayerProjection A D S x z n ≫
        (selectedPathModuleEvaluationIso A D S (fun w => w.length = n + 1) z (op x)).inv =
      (moduleEvaluation A D x).map (lengthLayerModuleProjection A D S z n)
    rw [Category.id_comp, lengthLayerModuleProjection_eval]

instance lengthModuleTransition_hasCokernel (S : Set D) (z : D) (n : ℕ) :
    HasCokernel (lengthModuleTransition A D S z (Nat.le_succ n)) :=
  HasColimit.mk ⟨_, lengthLayerModule_isColimit A D S z n⟩

/-- 長さの随伴次数部分と固定長 path 加群との同型。 -/
def lengthModuleGradedIso (S : Set D) (z : D) (n : ℕ) :
    cokernel (lengthModuleTransition A D S z (Nat.le_succ n)) ≅
      selectedPathModule A D S (fun w => w.length = n + 1) z :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (lengthLayerModule_isColimit A D S z n)

@[reassoc] lemma lengthModuleGradedIso_π (S : Set D) (z : D) (n : ℕ) :
    cokernel.π (lengthModuleTransition A D S z (Nat.le_succ n)) ≫
        (lengthModuleGradedIso A D S z n).hom = lengthLayerModuleProjection A D S z n :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- 加群圏での随伴次数部分の、S 上の自由加群による表示。 -/
def lengthModuleGradedFreeIso (S : Set D) (z : D) (n : ℕ) :
    cokernel (lengthModuleTransition A D S z (Nat.le_succ n)) ≅
      ∐ (fun p : S × LengthWord S n =>
        (freeAt p.1.val).obj (pathSuffixWeight A D p.2.val p.1 z)) :=
  lengthModuleGradedIso A D S z n ≪≫ fixedLengthModuleFreeIso A D S z n

end SerrePositivity.DifferentialGraded.DGQuotient
