module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointCorrectionProjectionComponents
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetFiber
public import SerrePositivity.EInfinity.FrameHom.NerveColumnComponentArrow
public import SerrePositivity.EInfinity.FrameHom.NerveColumnWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoComponentPre
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoVertexEvaluation

/-!
概要：元の全標的置換の同じ逆成分を、同じ置換単位の実射の類へ照合する。
方針：元の弱自然変換の同型と前合成の同じ点を、既存の成分評価の法則で計算する。
規約：同じ全同型の成分と端点を Arrow の等式で保持する。
使われ方：元の corrected pairing の単位ラベルの右射影の計算。
-/

@[expose] public section
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
local instance jointTargetPointValuesModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointTargetPointValuesFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全弱自然変換の同型の順成分は、同じ元の実射の類になる。 -/
lemma strictBETotModelWeakTransformationIso_component_arrow {J : Type (u+1)} [SmallCategory J]
    {F G : J ⥤ AsSmall.{u+1} (operad A).Algebra} (η : F ⟶ G)
    (hη : ∀ j, weakEquivalences (operad A).Algebra (AsSmall.down.map (η.app j))) (j : J) :
    Arrow.mk ((strictBETotModelWeakTransformationIso A η hη).app (nerveVertex j)).hom =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk (η.app j)).map (strictBETotModelSource A))) := by
  have he : ((strictBETotModelWeakTransformationIso A η hη).app (nerveVertex j)).hom =
      functorHomEvaluate (strictBETotModelWeakTransformationIso A η hη).hom (nerveVertex j) := by
    rw [FunctorIso.app_eq_evaluate]
    rfl
  rw [he]
  unfold strictBETotModelWeakTransformationIso
  rw [SerrePositivity.EInfinity.FrameHom.sameNerveTransformationPostIso_column]
  exact SerrePositivity.EInfinity.FrameHom.NerveColumn.hom_component_arrow _ _ _

/-- 元の全標的置換同型の順成分は、元の同じ置換単位の実射の類。 -/
lemma strictBETotTargetReplacementNativeIso_component_arrow (Y : AsSmall.{u+1} (operad A).Algebra) :
    Arrow.mk ((strictBETotTargetReplacementNativeIso A).app (nerveVertex Y)).hom =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotTargetReplacementUnit A).app Y)).map (strictBETotModelSource A))) := by
  change Arrow.mk ((strictBETotModelWeakTransformationIso A
    (strictBETotTargetReplacementUnit A) (strictBETotTargetReplacementUnit_weak A)).app
      (nerveVertex Y)).hom = _
  exact strictBETotModelWeakTransformationIso_component_arrow A _ _ _

/-- 元の実射上へ引き戻した標的比較の逆成分は、元の同じ置換単位の実射の類。 -/
lemma strictBETotJointSourceTargetReplacementIso_inv_component_arrow (t : StrictBETotJointSourceElements A) :
    Arrow.mk ((strictBETotJointSourceTargetReplacementIso A).app (nerveVertex t)).inv =
      Arrow.mk (HomotopyCategory.homMk
        ((nerve.edgeMk ((strictBETotTargetReplacementUnit A).app
          ((strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A).obj t))).map
            (strictBETotModelSource A))) := by
  change Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app
    (((strictBETotTargetReplacementNativeIso A).precomp
      (nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A))).symm)
    (nerveVertex t)).inv) = _
  rw [FunctorIso.app_symm, Iso.symm_inv]
  have hp := eq_of_heq (functorIso_app_precomp_heq (strictBETotTargetReplacementNativeIso A)
    (nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A))
    (nerveVertex t))
  rw [hp]
  have hv : (nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A)).app
      (Opposite.op ⦋0⦌) (nerveVertex t) =
      nerveVertex ((strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A).obj t) :=
    ComposableArrows.ext₀ rfl
  have ha := congrArg (fun v => Arrow.mk ((strictBETotTargetReplacementNativeIso A).app v).hom) hv
  exact ha.trans (strictBETotTargetReplacementNativeIso_component_arrow A _)

/-- 元の全要素の標的で読む全置換単位は、元の標的の同じ置換単位。 -/
lemma strictBETotJointSourceTargetReplacementUnit_parameter_component (t : StrictBETotJointSourceElements A) :
    (strictBETotTargetReplacementUnit A).app
      ((strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A).obj t) =
    (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
      ((rightFrameReplacementUnit (rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2) := rfl
end SerrePositivity.EInfinity.BarrattEccles

end
