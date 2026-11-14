module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourcePairing
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotModelWeakTransformation

/-!
概要：元のBEの標的置換単位を全図式で反転し、同じ全実射の標的から元の標的へ戻す。
方針：元のright-frame置換単位を同じモデル源へ送り、元の全要素の射影へ前合成する。
規約：元の単位と元のモデル源の同じ全関手同型を使う。
使われ方：R03dの同じpairingの標的端点の正規化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]
local instance jointTargetReplacementModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointTargetReplacementFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じ元の標的置換を、元のモデル源の通常の添字にする。 -/
def strictBETotTargetReplacement :
    AsSmall.{u+1} (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra :=
  AsSmall.down ⋙ rightFrameReplacement (rightFrameFamily A) ⋙ AsSmall.up

/-- 元の標的置換単位を同じ全添字で記録する。 -/
def strictBETotTargetReplacementUnit :
    𝟭 (AsSmall.{u+1} (operad A).Algebra) ⟶ strictBETotTargetReplacement A :=
  Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down (rightFrameReplacementUnit (rightFrameFamily A))) AsSmall.up

/-- 同じ元の標的置換単位は全モデル弱同値。 -/
theorem strictBETotTargetReplacementUnit_weak (Y : AsSmall.{u+1} (operad A).Algebra) :
    weakEquivalences (operad A).Algebra
      (AsSmall.down.map ((strictBETotTargetReplacementUnit A).app Y)) :=
  (rightFrameReplacementUnit_trivialCofibration (rightFrameFamily A) (AsSmall.down.obj Y)).2

/-- 元の全標的置換単位自身を同じモデル源で反転する全関手同型。 -/
def strictBETotTargetReplacementNativeIso :
    FunctorIso (strictBETotModelSource A)
      (nerveMap (strictBETotTargetReplacement A) ≫ strictBETotModelSource A) := by
  have h := strictBETotModelWeakTransformationIso A
    (F := 𝟭 (AsSmall.{u+1} (operad A).Algebra)) (G := strictBETotTargetReplacement A)
    (strictBETotTargetReplacementUnit A) (strictBETotTargetReplacementUnit_weak A)
  have hi : nerveMap (𝟭 (AsSmall.{u+1} (operad A).Algebra)) = 𝟙 _ := rfl
  rw [hi, Category.id_comp] at h
  exact h

/-- 元の実射の標的は、元の全標的射影に同じ置換を合成したもの。 -/
theorem strictBETotJointSourceCodomain_replacement :
    FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)) =
    strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A ⋙
      strictBETotTargetReplacement A := rfl

/-- 元の全実射のnativeな標的の全図式。 -/
def strictBETotJointSourceNativeCodomain :
    nerve (StrictBETotJointSourceElements A) ⟶ CAlg_R A :=
  nerveMap (FrameHom.liftedSourceFrameArrowCodomain (strictBETotJointSourceFrame A)
    (rightFrameReplacement (rightFrameFamily A))) ≫ strictBETotModelSource A

/-- 同じ全実射の元の標的のnativeな全図式。 -/
def strictBETotJointSourceOriginalNativeCodomain :
    nerve (StrictBETotJointSourceElements A) ⟶ CAlg_R A :=
  nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A) ≫
    strictBETotModelSource A

/-- 元の全標的置換単位の同じ逆を、元の全実射の標的へ引き戻した比較。 -/
def strictBETotJointSourceTargetReplacementIso :
    FunctorIso (strictBETotJointSourceNativeCodomain A)
      (strictBETotJointSourceOriginalNativeCodomain A) := by
  have h := (strictBETotTargetReplacementNativeIso A).precomp
    (nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A))
  change FunctorIso (strictBETotJointSourceOriginalNativeCodomain A)
    (nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A ⋙
      strictBETotTargetReplacement A) ≫ strictBETotModelSource A) at h
  rw [← strictBETotJointSourceCodomain_replacement] at h
  exact h.symm
end SerrePositivity.EInfinity.BarrattEccles
