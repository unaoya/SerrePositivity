module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofFrame
public import SerrePositivity.EInfinity.Hammock.AsSmallComposition

/-!
概要：元の fiber roof のラベルを同じ三列の nerve へ合わせる。
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
local instance jointRoofGraphLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofGraphLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 同じ二列への全単体の写像は、元の係数同型とAsSmall比較そのもの。 -/
theorem strictBETotJointSourceRoofFrameZigzag_nerve
    (P : strictBETotJointHomIndex A) :
    (elementsOppositeUniverseNerveIso.{u+1,u}
      ((SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        (strictBETotJointRoofResolution A P).obj).obj
          ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2))).hom ≫
      FrameHom.frameLeftRoofNerveMap (weakEquivalences (operad A).Algebra)
        (strictBETotJointRoofResolution A P).obj
        (strictBETotJointRoofResolution A P).augmentation
        (strictBETotJointRoofResolution A P).augmentation_weakEquivalence
        (fun f => (strictBETotJointRoofResolution A P).homotopicallyConstant f) ≫
      (Hammock.AsSmallComparison.graphIso (weakEquivalences (operad A).Algebra)
        (framedLimitProbe A (AsSmall.down.obj P).1.unop)
        ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
        LeftRoof.word).hom =
      nerveMap (strictBETotJointSourceRoofFrameZigzag A P) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.hext (fun i => ?_) ?_
  · apply ZigzagExt.object_ext
    · intro k
      fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl
  · intro i j f
    apply ZigzagExt.hom_hext
    · apply ZigzagExt.object_ext
      · intro k
        fin_cases k <;> rfl
      · intro k
        fin_cases k <;> rfl
    · apply ZigzagExt.object_ext
      · intro k
        fin_cases k <;> rfl
      · intro k
        fin_cases k <;> rfl
    · intro k
      fin_cases k <;> rfl

end SerrePositivity.EInfinity.BarrattEccles
