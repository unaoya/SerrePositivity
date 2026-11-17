module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointCorrectionProjectionComponents
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceTargetFiber
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnComponentArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentPre
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoVertexEvaluation

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の全標的置換の同じ逆成分を、同じ置換単位の実射の類へ照合する。
方針：元の弱自然変換の同型と前合成の同じ点を、既存の成分評価の法則で計算する。
規約：同じ全同型の成分と端点を Arrow の等式で保持する。
使われ方：元の corrected pairing の単位ラベルの右射影の計算。
-/

@[expose] public section
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
variable (A : Type u) [CommRing A]
local instance jointTargetPointValuesModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointTargetPointValuesFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の全弱自然変換の同型の順成分は、同じ元の実射の類になる。 -/
lemma strictBETotModelWeakTransformationIso_component_arrow {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (AsSmall.down.map (η.app j))) (j : J) :
    Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso A η hη).app (nerveVertex j)).hom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk (η.app j)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  have he : ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso A η hη).app (nerveVertex j)).hom =
      functorHomEvaluate (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso A η hη).hom (nerveVertex j) := by
    rw [FunctorIso.app_eq_evaluate]
    rfl
  rw [he]
  unfold _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sameNerveTransformationPostIso_column]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_component_arrow _ _ _

/-- 元の全標的置換同型の順成分は、元の同じ置換単位の実射の類。 -/
lemma strictBETotTargetReplacementNativeIso_component_arrow (Y : AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).app (nerveVertex Y)).hom =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit A).app Y)).map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  change Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso A
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit_weak A)).app
      (nerveVertex Y)).hom = _
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso_component_arrow A _ _ _

/-- 元の実射上へ引き戻した標的比較の逆成分は、元の同じ置換単位の実射の類。 -/
lemma strictBETotJointSourceTargetReplacementIso_inv_component_arrow (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso A).app (nerveVertex t)).inv =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit A).app
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj t))).map
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  change Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
    (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).precomp
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A))).symm)
    (nerveVertex t)).inv) = _
  rw [FunctorIso.app_symm, Iso.symm_inv]
  have hp := eq_of_heq (functorIso_app_precomp_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A)
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A))
    (nerveVertex t))
  rw [hp]
  have hv : (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A)).app
      (Opposite.op ⦋0⦌) (nerveVertex t) =
      nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj t) :=
    ComposableArrows.ext₀ rfl
  have ha := congrArg (fun v => Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).app v).hom) hv
  exact ha.trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso_component_arrow A _)

/-- 元の全要素の標的で読む全置換単位は、元の標的の同じ置換単位。 -/
lemma strictBETotJointSourceTargetReplacementUnit_parameter_component (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit A).app
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj t) =
    (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
      ((rightFrameReplacementUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2) := rfl
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
