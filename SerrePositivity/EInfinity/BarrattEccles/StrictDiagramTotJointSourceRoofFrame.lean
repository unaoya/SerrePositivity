module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRoofPinched
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixColumnRoof

/-!
概要：同じ全要素の fiber の元の resolution・augmentation・評価を記録する。
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
local instance jointRoofFrameLawModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointRoofFrameLawFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の試験対象の同じ probe に使った source-frame resolution。 -/
abbrev strictBETotJointRoofResolution (P : strictBETotJointHomIndex A) :=
  (SimplicialLocalization.modelSourceFrameFamily (C := (operad A).Algebra)).atObject
    (framedLimitProbe A (AsSmall.down.obj P).1.unop)

/-- 元の fiber のラベルを同じ resolution の次数の対象と射へ送る。 -/
def strictBETotJointSourceRoofFrameDiagram (P : strictBETotJointHomIndex A) :
    ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⥤
      (modelRelativeCategory (operad A).Algebra).category where
  obj s := (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).obj ((strictBETotJointRoofResolution A P).obj.obj s.unop.obj.unop)
  map f := (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).obj.map f.unop.down.hom.unop)
  map_id s := by
    change (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).obj.map (𝟙 _)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    change (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).obj.map
      (f.unop.down.hom.unop ≫ g.unop.down.hom.unop)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]

/-- 同じ次数の resolution の増大写像を元の probe へ送る全変換。 -/
def strictBETotJointSourceRoofFrameAugmentation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra
          (framedLimitProbe A (AsSmall.down.obj P).1.unop)) where
  app s := (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).augmentation.app s.unop.obj.unop)
  naturality s t f := by
    change (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).obj.map f.unop.down.hom.unop) ≫
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).augmentation.app t.unop.obj.unop) =
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).augmentation.app s.unop.obj.unop) ≫ 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, Category.comp_id]
    exact congrArg ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map) ((strictBETotJointRoofResolution A P).augmentation.naturality
      f.unop.down.hom.unop |>.trans (Category.comp_id _))

/-- 元の fiber の射のラベルを、同じ標的置換への評価として送る全変換。 -/
def strictBETotJointSourceRoofFrameEvaluation (P : strictBETotJointHomIndex A) :
    strictBETotJointSourceRoofFrameDiagram A P ⟶
      (CategoryTheory.Functor.const _).obj
        (modelRelativeObject (operad A).Algebra
          ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)) where
  app s := (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map s.unop.val.down
  naturality s t f := by
    change (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map ((strictBETotJointRoofResolution A P).obj.map f.unop.down.hom.unop) ≫
      (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map t.unop.val.down = (AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map s.unop.val.down ≫ 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, Category.comp_id]
    apply congrArg ((AsSmall.up : (operad A).Algebra ⥤ AsSmall.{u+1} (operad A).Algebra).map)
    exact congrArg ULift.down f.unop.down.map_val

/-- 同じ resolution の増大写像の各成分は、元のモデル弱同値。 -/
lemma strictBETotJointSourceRoofFrameAugmentation_weak
    (P : strictBETotJointHomIndex A)
    (s : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFrameAugmentation A P).app s) :=
  (strictBETotJointRoofResolution A P).augmentation_weakEquivalence _

/-- 同じ source frame の次数作用素の像は、元のモデル弱同値。 -/
lemma strictBETotJointSourceRoofFrameDiagram_weak
    (P : strictBETotJointHomIndex A)
    {s t : ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ}
    (f : s ⟶ t) :
    (modelRelativeCategory (operad A).Algebra).weakEquivalences
      ((strictBETotJointSourceRoofFrameDiagram A P).map f) :=
  (strictBETotJointRoofResolution A P).homotopicallyConstant _

/-- 同じfiberの全ラベルとaugmentationからなる元の二列roof図式。 -/
def strictBETotJointSourceRoofFrameZigzag (P : strictBETotJointHomIndex A) :=
  LeftRoof.diagram (modelRelativeCategory (operad A).Algebra).weakEquivalences
    (strictBETotJointSourceRoofFrameDiagram A P)
    (strictBETotJointSourceRoofFrameAugmentation A P)
    (strictBETotJointSourceRoofFrameAugmentation_weak A P)
    (strictBETotJointSourceRoofFrameEvaluation A P)
    (strictBETotJointSourceRoofFrameDiagram_weak A P)

end SerrePositivity.EInfinity.BarrattEccles
