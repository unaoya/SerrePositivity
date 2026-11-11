module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ConeCoefficient
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-! cone の三項行列を全 Hom end 内で構成し、指定比較ホモトピーを保持する閉零 dg 加群射にする。 -/
@[expose] public section
open CategoryTheory Limits MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
  (f : ForgetEnrichment.of (Complex R) X ⟶ ForgetEnrichment.of (Complex R) Y)

def dgGluingCommaConeElement :
    (moduleHom R C
      (ForgetEnrichment.to (Complex R)
        (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f)))
      (ForgetEnrichment.to (Complex R)
        (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f)))).X 0 :=
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f
  compose R (moduleConeInlElement R C b)
    (compose R (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) X.augmentation)).val
      (moduleConeFstElement R C a) (add_zero 1)) (add_neg_cancel 1) +
  compose R (moduleConeInrElement R C b)
    (compose R (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) Y.augmentation)).val
      (moduleConeSndElement R C a) (add_zero 0)) (add_zero 0) +
  compose R (moduleConeInrElement R C b)
    (compose R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedPrimitive R C D M X Y f)
      (moduleConeFstElement R C a) (add_neg_cancel 1)) (add_zero 0)

lemma dgGluingCommaConeElement_matrix (c : C) :
    (moduleHomπ R C _ _ c).f 0 (dgGluingCommaConeElement R C D M X Y f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMatrix
        ((moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f))
        ((moduleEvaluation R C c).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f))
        ((moduleEvaluation R C c).map X.augmentation)
        ((moduleEvaluation R C c).map Y.augmentation)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy R C D M X Y f c) := by
  simp only [dgGluingCommaConeElement, map_add]
  rw [moduleHomCompose_π, moduleHomCompose_π, moduleHomCompose_π,
    moduleHomCompose_π, moduleHomCompose_π, moduleHomCompose_π,
    moduleConeInlElement_π, moduleConeFstElement_π, moduleConeSndElement_π,
    moduleConeInrElement_π]
  rw [← moduleEvaluation_cochain R C c X.augmentation,
    ← moduleEvaluation_cochain R C c Y.augmentation]
  erw [moduleConeFstElement_π R C
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f) c,
    moduleConeInrElement_π R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f) c]
  change
    (((mappingCone.fst ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f))).val.comp
      (Cochain.ofHom ((moduleEvaluation R C c).map X.augmentation)) (add_zero 1)).comp
        (mappingCone.inl ((moduleEvaluation R C c).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f))) (add_neg_cancel 1) +
    ((mappingCone.snd ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f))).comp
      (Cochain.ofHom ((moduleEvaluation R C c).map Y.augmentation)) (add_zero 0)).comp
      (Cochain.ofHom (mappingCone.inr ((moduleEvaluation R C c).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f)))) (add_zero 0) +
    ((mappingCone.fst ((moduleEvaluation R C c).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f))).val.comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSquareHomotopy R C D M X Y f c) (add_neg_cancel 1)).comp
      (Cochain.ofHom (mappingCone.inr ((moduleEvaluation R C c).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f)))) (add_zero 0)) = _
  rfl

lemma dgGluingCommaConeElement_eval (c : C) :
    (moduleHomπ R C _ _ c).f 0 (dgGluingCommaConeElement R C D M X Y f) =
      Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaConeCoefficient R C D M X Y f c) := by
  rw [dgGluingCommaConeElement_matrix]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeSquareMatrix_eq _ _ _ _ _ _

lemma dgGluingCommaConeElement_closed :
    (moduleHom R C
      (ForgetEnrichment.to (Complex R)
        (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f)))
      (ForgetEnrichment.to (Complex R)
        (moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f)))).d 0 1
      (dgGluingCommaConeElement R C D M X Y f) = 0 := by
  apply moduleHomElement_ext R C
  intro c
  rw [moduleHomElement_d_π, dgGluingCommaConeElement_eval, δ_ofHom, map_zero]

def dgGluingCommaConeMorphism :
    moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f) ⟶
      moduleCone R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f) :=
  ForgetEnrichment.homOf (Complex R)
    (unitFromCycle _ ⟨dgGluingCommaConeElement R C D M X Y f,
      dgGluingCommaConeElement_closed R C D M X Y f⟩)

lemma dgGluingCommaConeMorphism_eval (c : C) :
    (moduleEvaluation R C c).map (dgGluingCommaConeMorphism R C D M X Y f) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaConeCoefficient R C D M X Y f c := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain R C c (dgGluingCommaConeMorphism R C D M X Y f),
    dgGluingCommaConeMorphism, ForgetEnrichment.homTo_homOf]
  erw [cycleFromUnit_unitFromCycle]
  exact dgGluingCommaConeElement_eval R C D M X Y f c

lemma dgGluingCommaConeMorphism_inr :
    moduleConeInr R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedReplacementMap R C D M X Y f) ≫
      dgGluingCommaConeMorphism R C D M X Y f =
    Y.augmentation ≫ moduleConeInr R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaClosedSourceMap R C D M X Y f) := by
  apply moduleMorphism_ext R C
  intro c
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleConeInr_eval, moduleConeInr_eval, dgGluingCommaConeMorphism_eval]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaConeCoefficient_inr R C D M X Y f c

variable (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (g : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)

/-- 元の native gluing 射の、全 dg 自然な cone 比較射。 -/
abbrev dgGluingConeMorphism :=
  dgGluingCommaConeMorphism R C D M
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M B)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M).onClosed.map g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
