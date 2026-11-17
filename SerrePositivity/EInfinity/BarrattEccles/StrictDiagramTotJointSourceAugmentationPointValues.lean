module

public import SerrePositivity.EInfinity.FrameHom.NerveColumnComponentArrow
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentPre
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceUnitLabel
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceOppositeAugmentation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoEvaluation

/-!
概要：元の全 augmentation の同じ成分を、元の実射の類へ照合する。
方針：同じ反転入力と前合成の成分評価を、既存の反転評価と列の実射の式で計算する。
規約：同じ全同型と元の点を保ち、端点も Arrow の等式で保持する。
使われ方：元の corrected pairing の単位ラベルの左右射影の計算。
-/

@[expose] public section
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
local instance jointAugmentationPointValuesModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointAugmentationPointValuesFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の反転入力の同じ頂点を戻すと、元の全パラメータの同じ頂点になる。 -/
lemma strictBETotJointSourceAugmentationInput_vertex (t : StrictBETotJointSourceElements A) :
    SSet.opObjEquiv ((strictBETotJointSourceAugmentationInput A).app
      (Opposite.op ⦋0⦌) (nerveVertex t)) =
      nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop) :=
  by
    change SSet.opObjEquiv ((nerveOppositeIso
      (C := strictBETotJointSourceFrameIndex A)).inv.app (Opposite.op ⦋0⦌)
        ((nerveMap (strictBETotJointSourceParameterIndex A)).app _ (nerveVertex t))) = _
    rw [nerveOppositeIso_inv_apply]
    apply ComposableArrows.ext₀
    rfl

/-- 元の全 augmentation の同じ成分は、元の増大写像と probe 比較の同じ合成。 -/
lemma strictBETotJointSourceFrameAugmentation_parameter_component (t : StrictBETotJointSourceElements A) :
    (strictBETotJointSourceFrameAugmentation A).app
      (((strictBETotJointSourceParameterIndex A).obj t).unop) =
    (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
      (((strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop) ≫
        framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop) := rfl

private lemma jointAugmentationAppInvArrowOfHEq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    Arrow.mk (e.app x).inv = Arrow.mk (e'.app x).inv := by
  subst f' g'
  cases he
  rfl

/-- 元の全 augmentation の順成分の射は、元の同じ実射の類を端点込みで回収する。 -/
lemma strictBETotJointSourceFrameAugmentation_component_arrow (t : StrictBETotJointSourceElements A) :
    Arrow.mk ((strictBETotJointSourceFrameAugmentationIso A).app
      (nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop))).hom =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app
          (((strictBETotJointSourceParameterIndex A).obj t).unop))).map
            (strictBETotModelSource A))) := by
  have he : ((strictBETotJointSourceFrameAugmentationIso A).app
      (nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop))).hom =
      functorHomEvaluate (strictBETotJointSourceFrameAugmentationIso A).hom
        (nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop)) := by
    rw [FunctorIso.app_eq_evaluate]
    rfl
  rw [he]
  change Arrow.mk (functorHomEvaluate
    (nerveTransformationPostIso (strictBETotJointSourceFrameAugmentation A)
      (strictBETotModelSource A) (strictBETotJointSourceFrameAugmentation_inverted A)).hom _) = _
  rw [SerrePositivity.EInfinity.FrameHom.sameNerveTransformationPostIso_column]
  exact SerrePositivity.EInfinity.FrameHom.NerveColumn.hom_component_arrow _ _ _

/-- 元の反変 augmentation の逆成分を戻すと、元の同じ実射の類を端点込みで回収する。 -/
lemma strictBETotJointSourceAugmentationDomainIso_inv_component_arrow (t : StrictBETotJointSourceElements A) :
    Arrow.mk (((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((strictBETotJointSourceAugmentationDomainIso A).app (nerveVertex t)).inv).unop) =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotJointSourceFrameAugmentation A).app
          (((strictBETotJointSourceParameterIndex A).obj t).unop))).map
            (strictBETotModelSource A))) := by
  have h₀ := jointAugmentationAppInvArrowOfHEq (strictBETotJointSourceAugmentationDomainIso A)
    ((strictBETotJointSourceFrameAugmentationIso A).op.precomp
      (strictBETotJointSourceAugmentationInput A))
    (strictBETotJointSourceAugmentationInput_evaluation A).symm
    (strictBETotJointSourceAugmentationInput_constant A).symm
    (strictBETotJointSourceAugmentationDomainIso_value A) (nerveVertex t)
  have hp := eq_of_heq (functorIso_app_precomp_heq
    (strictBETotJointSourceFrameAugmentationIso A).op
    (strictBETotJointSourceAugmentationInput A) (nerveVertex t))
  rw [hp] at h₀
  have hv : (strictBETotJointSourceAugmentationInput A).app
      (Opposite.op ⦋0⦌) (nerveVertex t) =
      SSet.opObjEquiv.symm (nerveVertex (((strictBETotJointSourceParameterIndex A).obj t).unop)) :=
    (SSet.opObjEquiv.eq_symm_apply).mpr (strictBETotJointSourceAugmentationInput_vertex A t)
  have harg := congrArg
    (fun v : ((nerve (strictBETotJointSourceFrameIndex A)).op) _⦋0⦌ =>
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (strictBETotJointSourceFrameAugmentationIso A).op v).inv)) hv
  have h₀' := h₀.trans harg
  have h₁ := congrArg (fun z : Arrow (hoFunctor.obj (CAlg_R A).op) =>
    Arrow.mk (((homotopyOppositeEquivalence (CAlg_R A)).functor.map z.hom).unop)) h₀'
  simp only [Arrow.mk_hom, functorIso_op_app_inv, Quiver.Hom.unop_op] at h₁
  exact h₁.trans (strictBETotJointSourceFrameAugmentation_component_arrow A t)
end SerrePositivity.EInfinity.BarrattEccles

end
