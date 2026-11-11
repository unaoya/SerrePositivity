module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Composition

/-! 実 comma の閉射から、元の次数 −1 成分を保つ全対象での比較ホモトピーを構成する。 -/
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

def dgGluingCommaClosedPrimitive :
    (homObject R (RightModule R C) X.replacement (M.toFunctor.obj Y.source)).X (-1) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor X Y).v 0 (-1) rfl
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val

lemma dgGluingCommaClosedPrimitive_boundary :
    (homObject R (RightModule R C) X.replacement (M.toFunctor.obj Y.source)).d (-1) 0
      (dgGluingCommaClosedPrimitive R C D M X Y f) =
    -(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R D (RightModule R C) M.toFunctor X Y).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMinusOneCochain_boundary_closed_zero
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R D (RightModule R C) M.toFunctor X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R D (RightModule R C) M.toFunctor X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive_boundary R D (RightModule R C) M.toFunctor X Y)
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).property

def dgGluingCommaClosedSquareHomotopy (c : C) :
    Cochain ((moduleEvaluation R C c).obj (ForgetEnrichment.of (Complex R) X.replacement))
      ((moduleEvaluation R C c).obj
        (ForgetEnrichment.of (Complex R) (M.toFunctor.obj Y.source))) (-1) :=
  (moduleHomπ R C X.replacement (M.toFunctor.obj Y.source) c).f (-1)
    (dgGluingCommaClosedPrimitive R C D M X Y f)

lemma dgGluingCommaClosedSquareHomotopy_boundary (c : C) :
    δ (-1) 0 (dgGluingCommaClosedSquareHomotopy R C D M X Y f c) =
    -(moduleHomπ R C X.replacement (M.toFunctor.obj Y.source) c).f 0
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R D (RightModule R C) M.toFunctor X Y).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val) := by
  rw [dgGluingCommaClosedSquareHomotopy, ← moduleHomElement_d_π]
  erw [dgGluingCommaClosedPrimitive_boundary R C D M X Y f, map_neg]

lemma dgGluingModuleClosedMap_cochain {S : Type w} [DGCategory R S]
    (G : DGFunctor R S (RightModule R C)) {x y : ClosedCategory R S} (k : x ⟶ y) (c : C) :
    (moduleHomπ R C (G.obj x) (G.obj y) c).f 0
      ((G.map x y).f 0 (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) k)).val) =
    Cochain.ofHom ((moduleEvaluation R C c).map (G.onClosed.map k)) := by
  have h := moduleEvaluation_cochain R C c (G.onClosed.map k)
  simpa only [EnrichedFunctor.forget, cycleFromUnit_postcomp] using! h.symm

def dgGluingCommaClosedSourceMap :
    ForgetEnrichment.of (Complex R) (M.toFunctor.obj X.source) ⟶
      ForgetEnrichment.of (Complex R) (M.toFunctor.obj Y.source) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D (RightModule R C) M.toFunctor).comp M.toFunctor).onClosed.map f

def dgGluingCommaClosedReplacementMap :
    ForgetEnrichment.of (Complex R) X.replacement ⟶
      ForgetEnrichment.of (Complex R) Y.replacement :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D (RightModule R C) M.toFunctor).onClosed.map f

lemma dgGluingCommaBoundary_eval (c : C) :
    (moduleHomπ R C X.replacement (M.toFunctor.obj Y.source) c).f 0
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R D (RightModule R C) M.toFunctor X Y).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val) =
    Cochain.ofHom (
      (moduleEvaluation R C c).map X.augmentation ≫
        (moduleEvaluation R C c).map
          (dgGluingCommaClosedSourceMap R C D M X Y f) -
      (moduleEvaluation R C c).map
        (dgGluingCommaClosedReplacementMap R C D M X Y f) ≫
          (moduleEvaluation R C c).map Y.augmentation) := by
  let t := (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val
  have hL := congrArg (fun q ↦ q.f 0
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t))
    (moduleHomWhiskerLeft_π R C
      (M := ForgetEnrichment.of (Complex R) X.replacement) Y.augmentation c)
  change (moduleHomπ R C X.replacement (M.toFunctor.obj Y.source) c).f 0
    ((eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
      Y.augmentation).f 0
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t)) =
    ((moduleHomπ R C X.replacement Y.replacement c).f 0
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t)).comp
      (Cochain.ofHom ((moduleEvaluation R C c).map Y.augmentation)) (add_zero 0) at hL
  change (moduleHomπ R C X.replacement (M.toFunctor.obj Y.source) c).f 0
    ((eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (M.toFunctor.obj Y.source))).f 0
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t) -
     (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) X.replacement)
       Y.augmentation).f 0
       ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t)) = _
  rw [map_sub]
  erw [moduleHomWhiskerRight_apply_π R C
    (P := ForgetEnrichment.of (Complex R) (M.toFunctor.obj Y.source)) X.augmentation 0
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t) c, hL]
  have ha := dgGluingModuleClosedMap_cochain R C
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacement R D (RightModule R C) M.toFunctor) f c
  have hb := dgGluingModuleClosedMap_cochain R C
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSource R D (RightModule R C) M.toFunctor).comp M.toFunctor) f c
  change (moduleHomπ R C X.replacement Y.replacement c).f 0
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t) = _ at ha
  change (moduleHomπ R C (M.toFunctor.obj X.source) (M.toFunctor.obj Y.source) c).f 0
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R D (RightModule R C) M.toFunctor X Y).f 0 t) = _ at hb
  erw [ha, hb, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_sub]
  rfl

lemma dgGluingCommaClosedSquareHomotopy_equation (c : C) :
    δ (-1) 0 (dgGluingCommaClosedSquareHomotopy R C D M X Y f c) +
    Cochain.ofHom (
      (moduleEvaluation R C c).map X.augmentation ≫
        (moduleEvaluation R C c).map (dgGluingCommaClosedSourceMap R C D M X Y f) -
      (moduleEvaluation R C c).map (dgGluingCommaClosedReplacementMap R C D M X Y f) ≫
        (moduleEvaluation R C c).map Y.augmentation) = 0 := by
  rw [dgGluingCommaClosedSquareHomotopy_boundary, dgGluingCommaBoundary_eval]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
