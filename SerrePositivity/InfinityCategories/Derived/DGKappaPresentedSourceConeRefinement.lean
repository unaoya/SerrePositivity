module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceCommonOperations
public import SerrePositivity.InfinityCategories.Derived.DGModuleFamilyHomotopyPretriangulated
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceShift
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceZero
/-!
概要：共通の小出発提示で閉射を精密化できれば、提示模型の cone 被覆と前三角性が従う。
方針：端点のホモトピー同型と可換な第一辺から標準 cone 三角形全体を比較する。
規約：係数の精密化の存在を明示入力に保持し、任意閉射への存在証明と区別する。
使われ方：c′ ゲート3の未証明境界を特定し、ゲート5の b 一般判定との接続を検査する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D]
  (κ : Cardinal.{u})
local notation "I" => DGKappaPresentedSourceObject R D κ
local notation "V" => dgKappaPresentedSourceValue R D κ
local notation "K" => moduleToHomotopy R D

structure DGKappaPresentedClosedArrowRefinement
    {M N : ModuleCategory R D} (f : M ⟶ N) where
  code : DGCategoryPresentationCode R κ
  arrow : DGFunctor R (code.Objects R κ) D
  sourceSeed : (dgKappaClosedProjectiveFamily R (code.Objects R κ) κ).1
  targetSeed : (dgKappaClosedProjectiveFamily R (code.Objects R κ) κ).1
  sourceMap : dgKappaPresentedSeedAt R κ code sourceSeed ⟶
    dgKappaPresentedSeedAt R κ code targetSeed
  sourceIso : (moduleToHomotopy R D).obj ((dgModuleExtension R (code.Objects R κ) D arrow).onClosed.obj
    (dgKappaPresentedSeedAt R κ code sourceSeed)) ≅ (moduleToHomotopy R D).obj M
  targetIso : (moduleToHomotopy R D).obj ((dgModuleExtension R (code.Objects R κ) D arrow).onClosed.obj
    (dgKappaPresentedSeedAt R κ code targetSeed)) ≅ (moduleToHomotopy R D).obj N
  comm : (moduleToHomotopy R D).map ((dgModuleExtension R (code.Objects R κ) D arrow).onClosed.map sourceMap) ≫
    targetIso.hom = sourceIso.hom ≫ (moduleToHomotopy R D).map f

variable (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
include hκ hreg

lemma dgKappaPresentedClosedArrowRefinement_cone
    {M N : ModuleCategory R D} (f : M ⟶ N)
    (r : DGKappaPresentedClosedArrowRefinement R D κ f) :
    ∃ Y : I, Nonempty ((moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R) (V Y)) ≅
      (moduleToHomotopy R D).obj (moduleCone R D f)) := by
  let g := (dgModuleExtension R (r.code.Objects R κ) D r.arrow).onClosed.map r.sourceMap
  let e := isoTriangleOfIso₁₂
    (moduleHomotopyConeTriangle R D g) (moduleHomotopyConeTriangle R D f)
    (moduleHomotopyConeTriangle_distinguished R D g)
    (moduleHomotopyConeTriangle_distinguished R D f) r.sourceIso r.targetIso r.comm
  exact ⟨dgKappaPresentedSourceCommonCone R D κ hκ hreg
    r.code r.arrow r.sourceSeed r.targetSeed r.sourceMap,
    ⟨(moduleToHomotopy R D).mapIso (dgKappaPresentedSourceCommonConeIso R D κ hκ hreg
      r.code r.arrow r.sourceSeed r.targetSeed r.sourceMap) ≪≫ (Triangle.π₃).mapIso e⟩⟩

lemma dgKappaPresentedSource_isDGPretriangulated_of_arrowRefinement
    (hrefine : ∀ {X Y : ClosedCategory R I} (f : X ⟶ Y),
      Nonempty (DGKappaPresentedClosedArrowRefinement R D κ
        ((dgKappaPresentedSourceEvaluation R D κ).onClosed.map f))) :
    IsDGPretriangulated R I := by
  apply dgModuleFamily_isDGPretriangulated_of_homotopy_cones R D I V
  · exact ⟨dgKappaPresentedSourceZero R κ hκ D,
      dgKappaPresentedSourceZero_isZero R κ hκ D⟩
  · intro X s
    exact ⟨dgKappaPresentedSourceShift R κ hκ hreg D X s,
      ⟨(dgKappaPresentedSourceShiftIso R κ hκ hreg D X s).symm⟩⟩
  · intro X Y f
    obtain ⟨r⟩ := hrefine f
    obtain ⟨Z, ⟨e⟩⟩ := dgKappaPresentedClosedArrowRefinement_cone R D κ hκ hreg _ r
    exact ⟨Z, ⟨e.symm⟩⟩

end SerrePositivity.InfinityCategories
