module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonPathModule
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonGradedTensor
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFiltrationAction
public import SerrePositivity.DifferentialGraded.Module.Colimits

/-! # 固定長 path の直和を右 dg 加群として表す -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [DGCategory A D] in
lemma selectedComplexColimits (S : Set D) (P : Word S → Prop) :
    HasColimitsOfShape (Discrete {w : Word S // P w}) (Complex A) := by
  have : HasColimitsOfShape (Discrete {w : Word S // P w}) (ModuleCat.{u} A) :=
    hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{u} {w : Word S // P w}).symm)
  exact ⟨fun F => HasColimit.mk
    ⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩

/-- 指定された word 部分集合の path 加群の直和。 -/
abbrev selectedPathModule (S : Set D) (P : Word S → Prop) (z : D) : ModuleCategory A D :=
  ∐ (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z))

def selectedPathModuleEvaluationIso (S : Set D) (P : Word S → Prop) (z : D) (x : Dᵒᵖ) :
    (moduleEvaluation A D x.unop).obj (selectedPathModule A D S P z) ≅
      selectedHom A D S P x.unop z := by
  have := selectedComplexColimits A D S P
  exact PreservesCoproduct.iso (moduleEvaluation A D x.unop)
      (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z)) ≪≫
    Sigma.mapIso
      (f := fun w : {w : Word S // P w} => (moduleEvaluation A D x.unop).obj
        (ForgetEnrichment.of (Complex A) (pathModule A D w.val z)))
      (g := fun w : {w : Word S // P w} => term A D w.val x.unop z)
      (fun w => pathModuleValueIso A D w.val z x)

@[reassoc] lemma selectedPathModuleEvaluationIso_ι (S : Set D) (P : Word S → Prop)
    (z : D) (x : Dᵒᵖ) (w : {w : Word S // P w}) :
    (moduleEvaluation A D x.unop).map (Sigma.ι
      (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z)) w) ≫
        (selectedPathModuleEvaluationIso A D S P z x).hom =
      (pathModuleValueIso A D w.val z x).hom ≫
        Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x.unop z) w := by
  have := selectedComplexColimits A D S P
  let hcol := isColimitOfHasCoproductOfPreservesColimit (moduleEvaluation A D x.unop)
    (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z))
  have h := hcol.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨w⟩
  change (moduleEvaluation A D x.unop).map (Sigma.ι
      (fun w : {w : Word S // P w} => ForgetEnrichment.of (Complex A) (pathModule A D w.val z)) w) ≫
    (PreservesCoproduct.iso (moduleEvaluation A D x.unop)
      (fun w : {w : Word S // P w} =>
        ForgetEnrichment.of (Complex A) (pathModule A D w.val z))).hom =
    Sigma.ι (fun w : {w : Word S // P w} => (moduleEvaluation A D x.unop).obj
      (ForgetEnrichment.of (Complex A) (pathModule A D w.val z))) w at h
  dsimp only [selectedPathModuleEvaluationIso, Iso.trans_hom]
  rw [← Category.assoc, h, Sigma.ι_mapIso_hom]

/-- 評価同型は、内部先頭作用と全次数で可換である。 -/
lemma selectedPathModuleEvaluationIso_action (S : Set D) (P : Word S → Prop) (z : D)
    (x y : Dᵒᵖ) :
    moduleActionChain A (ForgetEnrichment.to (Complex A) (selectedPathModule A D S P z)) x y ≫
        (selectedPathModuleEvaluationIso A D S P z y).hom =
      ((x ⟶[Complex A] y) ◁ (selectedPathModuleEvaluationIso A D S P z x).hom) ≫
        selectedPrepend A D S P y.unop x.unop z := by
  let F := fun w : {w : Word S // P w} =>
    ForgetEnrichment.of (Complex A) (pathModule A D w.val z)
  let hcol := isColimitOfHasCoproductOfPreservesColimit (moduleEvaluation A D x.unop) F
  apply (isColimitOfPreserves (tensorLeft (x ⟶[Complex A] y)) hcol).hom_ext
  rintro ⟨w⟩
  have hw := moduleMorphism_action_chain A D (Sigma.ι F w) x y
  change moduleActionChain A (pathModule A D w.val z) x y ≫
      (moduleEvaluation A D y.unop).map (Sigma.ι F w) =
    ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (Sigma.ι F w)) ≫
      moduleActionChain A (ForgetEnrichment.to (Complex A) (selectedPathModule A D S P z)) x y at hw
  change ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (Sigma.ι F w)) ≫
      (moduleActionChain A (ForgetEnrichment.to (Complex A) (selectedPathModule A D S P z)) x y ≫
        (selectedPathModuleEvaluationIso A D S P z y).hom) =
    ((x ⟶[Complex A] y) ◁ (moduleEvaluation A D x.unop).map (Sigma.ι F w)) ≫
      (((x ⟶[Complex A] y) ◁ (selectedPathModuleEvaluationIso A D S P z x).hom) ≫
        selectedPrepend A D S P y.unop x.unop z)
  calc
    _ = moduleActionChain A (pathModule A D w.val z) x y ≫
        ((moduleEvaluation A D y.unop).map (Sigma.ι F w) ≫
          (selectedPathModuleEvaluationIso A D S P z y).hom) := by
      rw [← Category.assoc, ← hw, Category.assoc]
    _ = moduleActionChain A (pathModule A D w.val z) x y ≫
        (pathModuleValueIso A D w.val z y).hom ≫
          Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y.unop z) w := by
      rw [selectedPathModuleEvaluationIso_ι]
    _ = ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w.val z x).hom) ≫
        prependMap A D w.val y.unop x.unop z ≫
          Sigma.ι (fun w : {w : Word S // P w} => term A D w.val y.unop z) w := by
      rw [← Category.assoc, pathModule_action_value, Category.assoc]
    _ = ((x ⟶[Complex A] y) ◁ (pathModuleValueIso A D w.val z x).hom) ≫
        ((x ⟶[Complex A] y) ◁
          Sigma.ι (fun w : {w : Word S // P w} => term A D w.val x.unop z) w) ≫
            selectedPrepend A D S P y.unop x.unop z := by
      exact congrArg (fun f => ((x ⟶[Complex A] y) ◁
        (pathModuleValueIso A D w.val z x).hom) ≫ f)
          (selectedPrepend_ι A D S P y.unop x.unop z w).symm
    _ = _ := by
      have he := congrArg (fun f => ((x ⟶[Complex A] y) ◁ f) ≫
        selectedPrepend A D S P y.unop x.unop z)
          (selectedPathModuleEvaluationIso_ι A D S P z x w)
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc] at he
      exact he.symm

/-- 正の固定長部分は、S 上の自由右加群の直和。 -/
def fixedLengthModuleFreeIso (S : Set D) (z : D) (n : ℕ) :
    selectedPathModule A D S (fun w => w.length = n + 1) z ≅
      ∐ (fun p : S × LengthWord S n =>
        (freeAt p.1.val).obj (pathSuffixWeight A D p.2.val p.1 z)) :=
  (Sigma.whiskerEquiv (consLengthWordEquiv S n)
    (fun p => pathModuleFreeIso A D p.1 p.2.val z)).symm

end SerrePositivity.DifferentialGraded.DGQuotient
