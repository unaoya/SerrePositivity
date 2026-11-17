module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofNativeAugmentation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoWhisker
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveLeftOpInput
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation

/-!
概要：元の native 側の反変 augmentation 同型を同じ roof の全同型へ合わせる。
方針：既存の同じ図式・射・指定同型の合成則を使う。
規約：元の全パラメータと指定された値を保持する。
使われ方：IS-W2 R03h・R03d の native Hom と同じ roof の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.EInfinity.FrameHom
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open scoped Simplicial
namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointOppositeAugmentationLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointOppositeAugmentationLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

private lemma sameEqMp_heq_iff {α β γ : Sort u} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b := by cases h; rfl

/-- 元のfiber制限の反変入力を同じleftOpパラメータで表す。 -/
theorem strictBETotJointSourceAugmentationInput_fiber
    (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      strictBETotJointSourceAugmentationInput A =
    (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
      (nerveOppositeIso (C := ((simplicialElementsCatDiagram
        (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv) ≫
      SSet.opFunctor.map (nerveMap (strictBETotJointRoofParameterIndex A P)) := by
  change nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
    strictBETotJointSourceParameterIndex A) ≫
      (nerveOppositeIso (C := strictBETotJointSourceFrameIndex A)).inv = _
  exact sameNerveLeftOp_input _

/-- 表示を合わせた同じaugmentation同型の値を保持する。 -/
theorem strictBETotJointSourceAugmentationDomainIso_value :
    HEq (strictBETotJointSourceAugmentationDomainIso A)
      ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
        (strictBETotJointSourceAugmentationInput A)) := by
  unfold strictBETotJointSourceAugmentationDomainIso
  simp only [sameEqMp_heq_iff]
  rfl

/-- 元の同じaugmentation同型を、元の同じfiberの全写像へ制限する。 -/
theorem strictBETotJointSourceAugmentationDomainIso_fiber_value
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
        (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
          strictBETotJointSourceAugmentationInput A)) := by
  have h0 := sameFunctorIso_precomp_of_heq (strictBETotJointSourceAugmentationDomainIso A)
    ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
      (strictBETotJointSourceAugmentationInput A))
    (strictBETotJointSourceAugmentationInput_evaluation A).symm
    (strictBETotJointSourceAugmentationInput_constant A).symm
    (strictBETotJointSourceAugmentationDomainIso_value A)
    (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P))
  exact h0.trans (heq_of_eq (functorIso_precomp_precomp
    (strictBETotJointSourceFrameAugmentationIso A).op
    (strictBETotJointSourceAugmentationInput A)
    (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P))))

/-- 同じfiber上の反変augmentation同型は、同じ全パラメータで制限して反転した元の同型。 -/
theorem strictBETotJointSourceAugmentationDomainIso_fiber_parameter
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      (((strictBETotJointSourceFrameAugmentationIso A).precomp
        (nerveMap (strictBETotJointRoofParameterIndex A P))).op.precomp
          (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
            (nerveOppositeIso (C := ((simplicialElementsCatDiagram
              (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv)) := by
  let b := nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
    (nerveOppositeIso (C := ((simplicialElementsCatDiagram
      (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv
  have h0 := strictBETotJointSourceAugmentationDomainIso_fiber_value A P
  have h1 := functorIso_precomp_heq_of_map_eq (strictBETotJointSourceFrameAugmentationIso A).op
    (strictBETotJointSourceAugmentationInput_fiber A P)
  have h2 := functorIso_precomp_precomp (strictBETotJointSourceFrameAugmentationIso A).op
    (SSet.opFunctor.map (nerveMap (strictBETotJointRoofParameterIndex A P))) b
  have h3 := sameFunctorIso_precomp_of_heq
    ((strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (strictBETotJointRoofParameterIndex A P))).op
    ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
      (SSet.opFunctor.map (nerveMap (strictBETotJointRoofParameterIndex A P)))) rfl rfl
    (sameFunctorIso_op_precomp (strictBETotJointSourceFrameAugmentationIso A)
      (nerveMap (strictBETotJointRoofParameterIndex A P))) b
  exact h0.trans (h1.trans ((heq_of_eq h2.symm).trans h3.symm))

/-- 元の反変augmentation同型の同じfiber制限は、同じroofの列の同型そのもの。 -/
theorem strictBETotJointSourceAugmentationDomainIso_roof_restriction
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceAugmentationDomainIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      ((FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
        (strictBETotJointSourceRoofFrameDiagram A P)
        (strictBETotJointSourceRoofFullAugmentation A P)
        (strictBETotJointSourceRoofFullAugmentation_inverted A P)).op.precomp
          (nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
            (nerveOppositeIso (C := ((simplicialElementsCatDiagram
              (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv)) := by
  let b := nerveMap (opOp ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)) ≫
    (nerveOppositeIso (C := ((simplicialElementsCatDiagram
      (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ)).inv
  have hf : nerveMap (strictBETotJointRoofParameterIndex A P) ≫
      (nerveMap (strictBETotJointSourceFrameEvaluation A) ≫ strictBETotModelSource A) =
      nerveMap (strictBETotJointSourceRoofFrameDiagram A P) ≫ strictBETotModelSource A := by
    change nerveMap (strictBETotJointRoofParameterIndex A P ⋙
      strictBETotJointSourceFrameEvaluation A) ≫ strictBETotModelSource A = _
    rw [strictBETotJointRoofParameterIndex_evaluation]
  have hg : nerveMap (strictBETotJointRoofParameterIndex A P) ≫
      (nerveMap (strictBETotJointSourceFrameConstant A) ≫ strictBETotModelSource A) =
      nerveMap ((CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra (AsSmall.down.obj P).1.unop)) ≫
          strictBETotModelSource A := by
    change nerveMap (strictBETotJointRoofParameterIndex A P ⋙
      strictBETotJointSourceFrameConstant A) ≫ strictBETotModelSource A = _
    rw [strictBETotJointRoofParameterIndex_constant]
  have hop := sameFunctorIso_op_of_heq
    ((strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (strictBETotJointRoofParameterIndex A P)))
    (FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
      (strictBETotJointSourceRoofFrameDiagram A P)
      (strictBETotJointSourceRoofFullAugmentation A P)
      (strictBETotJointSourceRoofFullAugmentation_inverted A P)) hf hg
    (strictBETotJointSourceFrameAugmentationIso_roof_restriction A P)
  have hpre := sameFunctorIso_precomp_of_heq
    ((strictBETotJointSourceFrameAugmentationIso A).precomp
      (nerveMap (strictBETotJointRoofParameterIndex A P))).op
    (FrameHom.NerveColumn.augmentationIso (strictBETotModelSource A)
      (strictBETotJointSourceRoofFrameDiagram A P)
      (strictBETotJointSourceRoofFullAugmentation A P)
      (strictBETotJointSourceRoofFullAugmentation_inverted A P)).op
    (congrArg (fun f => SSet.opFunctor.map f) hf)
    (congrArg (fun f => SSet.opFunctor.map f) hg) hop b
  exact (strictBETotJointSourceAugmentationDomainIso_fiber_parameter A P).trans hpre

end SerrePositivity.EInfinity.BarrattEccles
