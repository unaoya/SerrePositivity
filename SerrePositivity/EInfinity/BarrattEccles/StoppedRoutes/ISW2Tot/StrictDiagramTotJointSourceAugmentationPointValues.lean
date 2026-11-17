module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnComponentArrow
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentPre
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceUnitLabel
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceOppositeAugmentation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIsoEvaluation

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の全 augmentation の同じ成分を、元の実射の類へ照合する。
方針：同じ反転入力と前合成の成分評価を、既存の反転評価と列の実射の式で計算する。
規約：同じ全同型と元の点を保ち、端点も Arrow の等式で保持する。
使われ方：元の corrected pairing の単位ラベルの左右射影の計算。
-/

@[expose] public section
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
variable (A : Type u) [CommRing A]
local instance jointAugmentationPointValuesModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointAugmentationPointValuesFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の反転入力の同じ頂点を戻すと、元の全パラメータの同じ頂点になる。 -/
lemma strictBETotJointSourceAugmentationInput_vertex (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    SSet.opObjEquiv ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput A).app
      (Opposite.op ⦋0⦌) (nerveVertex t)) =
      nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop) :=
  by
    change SSet.opObjEquiv ((nerveOppositeIso
      (C := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A)).inv.app (Opposite.op ⦋0⦌)
        ((nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A)).app _ (nerveVertex t))) = _
    rw [nerveOppositeIso_inv_apply]
    apply ComposableArrows.ext₀
    rfl

/-- 元の全 augmentation の同じ成分は、元の増大写像と probe 比較の同じ合成。 -/
lemma strictBETotJointSourceFrameAugmentation_parameter_component (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop) =
    (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
      (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop) ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop) := rfl

private lemma jointAugmentationAppInvArrowOfHEq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    Arrow.mk (e.app x).inv = Arrow.mk (e'.app x).inv := by
  subst f' g'
  cases he
  rfl

/-- 元の全 augmentation の順成分の射は、元の同じ実射の類を端点込みで回収する。 -/
lemma strictBETotJointSourceFrameAugmentation_component_arrow (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).app
      (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop))).hom =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app
          (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop))).map
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  have he : ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).app
      (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop))).hom =
      functorHomEvaluate (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).hom
        (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop)) := by
    rw [FunctorIso.app_eq_evaluate]
    rfl
  rw [he]
  change Arrow.mk (functorHomEvaluate
    (nerveTransformationPostIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_inverted A)).hom _) = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_column]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_component_arrow _ _ _

/-- 元の反変 augmentation の逆成分を戻すと、元の同じ実射の類を端点込みで回収する。 -/
lemma strictBETotJointSourceAugmentationDomainIso_inv_component_arrow (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    Arrow.mk (((homotopyOppositeEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)).functor.map
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A).app (nerveVertex t)).inv).unop) =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation A).app
          (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop))).map
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  have h₀ := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointAugmentationAppInvArrowOfHEq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A)
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).op.precomp
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput A))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput_evaluation A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput_constant A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso_value A) (nerveVertex t)
  have hp := eq_of_heq (functorIso_app_precomp_heq
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).op
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput A) (nerveVertex t))
  rw [hp] at h₀
  have hv : (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput A).app
      (Opposite.op ⦋0⦌) (nerveVertex t) =
      SSet.opObjEquiv.symm (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A).obj t).unop)) :=
    (SSet.opObjEquiv.eq_symm_apply).mpr (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationInput_vertex A t)
  have harg := congrArg
    (fun v : ((nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A)).op) _⦋0⦌ =>
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentationIso A).op v).inv)) hv
  have h₀' := h₀.trans harg
  have h₁ := congrArg (fun z : Arrow (hoFunctor.obj (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op) =>
    Arrow.mk (((homotopyOppositeEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)).functor.map z.hom).unop)) h₀'
  simp only [Arrow.mk_hom, functorIso_op_app_inv, Quiver.Hom.unop_op] at h₁
  exact h₁.trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_component_arrow A t)
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
