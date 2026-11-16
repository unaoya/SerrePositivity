module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPairing
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition

/-!
概要：同じfiber制限で元のpairing比較の全同型と指定された底のpathを保持する。
方針：元の全同型を前合成し、前後合成の交換則で元の射影等式を移す。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance jointNativeFiberPathModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeFiberPathFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩



/-- 元の同じpairing比較を、同じ元のfiber包含へ制限した全同型。 -/
def strictBETotJointSourceFiberPairingIso (P : strictBETotJointHomIndex A) :
    FunctorIso
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A)
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceNativePairing A) :=
  (strictBETotJointSourceCorrectedPairingIso A).precomp
    (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P)

/-- 制限した同じ全同型の射影も、元の指定された底のpathの同じ制限そのもの。 -/
theorem strictBETotJointSourceFiberPairingIso_postcomp (P : strictBETotJointHomIndex A) :
    (strictBETotJointSourceFiberPairingIso A P).postcomp
      (twistedArrowProjection (CAlg_R A)) =
      FunctorIso.precomp (eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A)
            (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P) := by
  rw [strictBETotJointSourceFiberPairingIso,
    SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp,
    strictBETotJointSourceCorrectedPairingIso_postcomp]
end SerrePositivity.EInfinity.BarrattEccles
