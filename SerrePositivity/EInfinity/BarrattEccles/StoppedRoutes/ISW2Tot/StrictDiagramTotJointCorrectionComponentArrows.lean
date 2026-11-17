module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceAugmentationPointValues
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceTargetPointValues
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointCorrectionComponent

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の補正比較の成分の実際の左右射影を、元の実射の類へ照合する。
方針：同じ全射影の指定値を成分で読み、元の augmentation と標的単位の計算を代入する。
規約：元の補正比較の成分自身の像を使い、端点は Arrow の等式で保持する。
使われ方：元の単位ラベルの合成則で両端を相殺する。
-/

@[expose] public section
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange
open _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
variable (A : Type u) [CommRing A]
local instance jointCorrectionComponentArrowsModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointCorrectionComponentArrowsFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

private lemma jointCorrectionAppHomArrowOfHEq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    Arrow.mk (e.app x).hom = Arrow.mk (e'.app x).hom := by
  subst f' g'
  cases he
  rfl

/-- 元の補正比較の同じ成分の左射影を戻すと、元の増大写像と probe 比較の実射の類になる。 -/
lemma strictBETotJointSourceCorrection_left_component_arrow (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    let f := ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    Arrow.mk (((homotopyOppositeEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).map f)).unop) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
          ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop ≫
            _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop))).map
              (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  dsimp only
  have h₀ := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointCorrectionAppHomArrowOfHEq
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_left A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_left A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectionIso_left_value A) (nerveVertex t)
  have hp := eq_of_heq (functorIso_app_postcomp_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (nerveVertex t))
  rw [hp, FunctorIso.app_symm, Iso.symm_hom] at h₀
  change Arrow.mk ((SSet.mapHomotopyCategory (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).map
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom) =
    Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso A).app (nerveVertex t)).inv at h₀
  have h₁ := congrArg (fun z : Arrow (hoFunctor.obj (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A).op) =>
    Arrow.mk (((homotopyOppositeEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)).functor.map z.hom).unop)) h₀
  simp only [Arrow.mk_hom] at h₁
  have h := h₁.trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceAugmentationDomainIso_inv_component_arrow A t)
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameAugmentation_parameter_component] at h
  exact h

/-- 元の補正比較の同じ成分の右射影は、元の標的置換単位の実射の類になる。 -/
lemma strictBETotJointSourceCorrection_right_component_arrow (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    let f := ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    Arrow.mk ((SSet.mapHomotopyCategory (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).map f) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).map
          ((rightFrameReplacementUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2))).map
            (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A))) := by
  dsimp only
  have h₀ := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointCorrectionAppHomArrowOfHEq
    ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso A).symm
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing_right A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing_right A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectionIso_right_value A) (nerveVertex t)
  have hp := eq_of_heq (functorIso_app_postcomp_heq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) (nerveVertex t))
  rw [hp, FunctorIso.app_symm, Iso.symm_hom] at h₀
  change Arrow.mk ((SSet.mapHomotopyCategory (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).map
      ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom) =
    Arrow.mk ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso A).app (nerveVertex t)).inv at h₀
  have h := h₀.trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementIso_inv_component_arrow A t)
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceTargetReplacementUnit_parameter_component] at h
  exact h
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
