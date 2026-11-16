module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointTargetReplacement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialElementsFiberFunctorLaws
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerCancellation

/-!
概要：元の同じ標的置換の全同型を同じ fiber へ制限する。
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
local instance jointTargetFiberLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointTargetFiberLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じfiber上の全標的添字は、元の同じ標的の定値関手。 -/
theorem strictBETotJointSourceTargetIndex_fiber (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
      strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A =
    (CategoryTheory.Functor.const _).obj ((strictBETotJointHomTargetIndex A).obj P) := by
  change (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
    simplicialTotalElementsProjection (strictBETotJointSourceCoefficients A)) ⋙
      strictBETotJointHomTargetIndex A = _
  rw [sameSimplicialElementsFiberFunctor_projection]
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro s t f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (strictBETotJointHomTargetIndex A).map_id P

/-- 同じ元の標的入力の全nerveも、同じ標的頂点の定値写像。 -/
theorem strictBETotJointSourceTargetIndex_nerve_fiber
    (P : strictBETotJointHomIndex A) :
    nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P) ≫
      nerveMap (strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A) =
    SSet.const (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)) := by
  change nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P ⋙
    strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomTargetIndex A) = _
  rw [strictBETotJointSourceTargetIndex_fiber]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  rfl


open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 指定された元の構成の値を保つ照合則。 -/
theorem strictBETotJointSourceTargetReplacementIso_fiber
    (P : strictBETotJointHomIndex A) :
    HEq ((strictBETotJointSourceTargetReplacementIso A).precomp
      (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P)))
      (((strictBETotTargetReplacementNativeIso A).precomp
        (SSet.const (X := nerve ((simplicialElementsCatDiagram
          (strictBETotJointSourceCoefficients A)).obj P))
          (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))))).symm := by
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (((strictBETotTargetReplacementNativeIso A).precomp
      (nerveMap (strictBETotJointSourceElementsProjection A ⋙
        strictBETotJointHomTargetIndex A))).symm)
    (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A) P))) _
  rw [← functorIso_precomp_symm, functorIso_precomp_precomp]
  have h0 := functorIso_precomp_heq_of_map_eq
    (strictBETotTargetReplacementNativeIso A).symm
    (strictBETotJointSourceTargetIndex_nerve_fiber A P)
  have h1 := functorIso_precomp_symm (strictBETotTargetReplacementNativeIso A)
    (SSet.const (X := nerve ((simplicialElementsCatDiagram
      (strictBETotJointSourceCoefficients A)).obj P))
        (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))
  exact HEq.trans h0 (heq_of_eq h1)

end SerrePositivity.EInfinity.BarrattEccles
