module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceAugmentationPointValues
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceTargetPointValues
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointCorrectionComponent

/-!
概要：元の補正比較の成分の実際の左右射影を、元の実射の類へ照合する。
方針：同じ全射影の指定値を成分で読み、元の augmentation と標的単位の計算を代入する。
規約：元の補正比較の成分自身の像を使い、端点は Arrow の等式で保持する。
使われ方：元の単位ラベルの合成則で両端を相殺する。
-/

@[expose] public section
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A]
local instance jointCorrectionComponentArrowsModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointCorrectionComponentArrowsFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

private lemma jointCorrectionAppHomArrowOfHEq {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g f' g' : X ⟶ Y} (e : FunctorIso f g) (e' : FunctorIso f' g')
    (hf : f = f') (hg : g = g') (he : HEq e e') (x : X _⦋0⦌) :
    Arrow.mk (e.app x).hom = Arrow.mk (e'.app x).hom := by
  subst f' g'
  cases he
  rfl

/-- 元の補正比較の同じ成分の左射影を戻すと、元の増大写像と probe 比較の実射の類になる。 -/
lemma strictBETotJointSourceCorrection_left_component_arrow (t : StrictBETotJointSourceElements A) :
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    Arrow.mk (((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map f)).unop) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          ((strictBETotJointRoofResolution A t.obj.1).augmentation.app t.obj.2.unop ≫
            framedLimitProbeComparison A (AsSmall.down.obj t.obj.1).1.unop))).map
              (strictBETotModelSource A))) := by
  dsimp only
  have h₀ := jointCorrectionAppHomArrowOfHEq
    ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseLeft (CAlg_R A)))
    (strictBETotJointSourceAugmentationDomainIso A).symm
    (strictBETotJointSourceCorrectedPairing_left A) (strictBETotJointSourceNativePairing_left A)
    (strictBETotJointSourceCorrectionIso_left_value A) (nerveVertex t)
  have hp := eq_of_heq (functorIso_app_postcomp_heq (strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseLeft (CAlg_R A)) (nerveVertex t))
  rw [hp, FunctorIso.app_symm, Iso.symm_hom] at h₀
  change Arrow.mk ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map
      ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom) =
    Arrow.mk ((strictBETotJointSourceAugmentationDomainIso A).app (nerveVertex t)).inv at h₀
  have h₁ := congrArg (fun z : Arrow (hoFunctor.obj (CAlg_R A).op) =>
    Arrow.mk (((homotopyOppositeEquivalence (CAlg_R A)).functor.map z.hom).unop)) h₀
  simp only [Arrow.mk_hom] at h₁
  have h := h₁.trans (strictBETotJointSourceAugmentationDomainIso_inv_component_arrow A t)
  rw [strictBETotJointSourceFrameAugmentation_parameter_component] at h
  exact h

/-- 元の補正比較の同じ成分の右射影は、元の標的置換単位の実射の類になる。 -/
lemma strictBETotJointSourceCorrection_right_component_arrow (t : StrictBETotJointSourceElements A) :
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    Arrow.mk ((SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map f) =
      Arrow.mk (HomotopyCategory.homMk ((nerve.edgeMk
        ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map
          ((rightFrameReplacementUnit (rightFrameFamily A)).app (AsSmall.down.obj t.obj.1).2))).map
            (strictBETotModelSource A))) := by
  dsimp only
  have h₀ := jointCorrectionAppHomArrowOfHEq
    ((strictBETotJointSourceCorrectedPairingIso A).postcomp (edgewiseRight (CAlg_R A)))
    (strictBETotJointSourceTargetReplacementIso A).symm
    (strictBETotJointSourceCorrectedPairing_right A) (strictBETotJointSourceNativePairing_right A)
    (strictBETotJointSourceCorrectionIso_right_value A) (nerveVertex t)
  have hp := eq_of_heq (functorIso_app_postcomp_heq (strictBETotJointSourceCorrectedPairingIso A)
    (edgewiseRight (CAlg_R A)) (nerveVertex t))
  rw [hp, FunctorIso.app_symm, Iso.symm_hom] at h₀
  change Arrow.mk ((SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map
      ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom) =
    Arrow.mk ((strictBETotJointSourceTargetReplacementIso A).app (nerveVertex t)).inv at h₀
  have h := h₀.trans (strictBETotJointSourceTargetReplacementIso_inv_component_arrow A t)
  rw [strictBETotJointSourceTargetReplacementUnit_parameter_component] at h
  exact h
end SerrePositivity.EInfinity.BarrattEccles

end
