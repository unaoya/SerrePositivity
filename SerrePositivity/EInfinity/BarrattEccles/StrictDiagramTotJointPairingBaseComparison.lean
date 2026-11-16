module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceAugmentationComparison
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointTargetReplacement
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorIsoPairing

/-!
概要：同じ全pairingの両端の比較を、元の二変数のnative入力との全関手同型にまとめる。
方針：元の全augmentationと全標的単位の比較を、既存のh Funの直積分解で組にする。
規約：元の両比較を保つ。同じ底上のpairingへの厳密化は別。
使われ方：元の全要素分類から正本Hom∞へのR03dの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (A : Type u) [CommRing A]
local instance jointPairingBaseModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointPairingBaseFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全pairingのnativeな底は、同じ始域と標的の組そのもの。 -/
theorem strictBETotJointSourceNativePairingBase_eq_lift :
    strictBETotJointSourceNativePairingBase A =
      lift (strictBETotJointSourceNativeDomain A) (strictBETotJointSourceNativeCodomain A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [strictBETotJointSourceNativePairingBase, strictBETotJointSourceNativeDomain,
      Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
  · simp only [strictBETotJointSourceNativePairingBase, strictBETotJointSourceNativeCodomain,
      Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd]

/-- 元の試験対象と標的の組は、元の二変数native入力の同じ射影による引き戻し。 -/
theorem strictBETotJointSourceOriginalNativeEndpoints_eq :
    lift (strictBETotJointSourceOriginalNativeDomain A)
      (strictBETotJointSourceOriginalNativeCodomain A) =
        nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A := by
  rw [strictBETotJointNativeHomInput, comp_lift]
  apply congrArg₂ lift
  · change (nerveMap (strictBETotJointSourceElementsProjection A) ≫
      nerveMap (strictBETotJointHomSourceIndex A)) ≫ _ = _
    simp only [Category.assoc]
  · change (nerveMap (strictBETotJointSourceElementsProjection A) ≫
      nerveMap (strictBETotJointHomTargetIndex A)) ≫ _ = _
    simp only [Category.assoc]

/-- 同じ全pairingのnativeな底を、元の二変数native入力へ全関手同型でつなぐ。 -/
def strictBETotJointSourceNativePairingBaseIso :
    FunctorIso (strictBETotJointSourceNativePairingBase A)
      (nerveMap (strictBETotJointSourceElementsProjection A) ≫ strictBETotJointNativeHomInput A) := by
  have h := functorIsoPair (strictBETotJointSourceAugmentationDomainIso A)
    (strictBETotJointSourceTargetReplacementIso A)
  rw [← strictBETotJointSourceNativePairingBase_eq_lift,
    strictBETotJointSourceOriginalNativeEndpoints_eq] at h
  exact h
end SerrePositivity.EInfinity.BarrattEccles
