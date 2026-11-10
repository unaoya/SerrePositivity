module
public import SerrePositivity.KST.Spectra.FreeInterval
public import
  SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderPushoutCompletion
public import
  SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderPushoutWeakEquivalence

/-! # 同じ Ex∞ 円柱押し出し候補の単射性と弱比較
概要：同じ Kan 候補への両比較は単射で、元の右標的比較は局所化可逆。
方針：実押し出しの単射性・弱比較へ同じ anodyne 単位を合成する。
規約：左比較は構造射候補であり、弱同値とは主張しない。使われ方：BF の帰納段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 同じ実候補の値は、元の Ex∞ による Kan 複体。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletion_kanComplex (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 同じ Kan 候補への単位は、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionUnit_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right :=
  Spectra.anodyne_mono _ (presentedPerfectDGKanAssemblyCylinderCompletionUnit_anodyne A r C)

/-- 元の左標的から同じ Kan 候補への比較は、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionLeftMap_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionLeftMap A r C).right := by
  let _ := presentedPerfectDGKanAssemblyCylinderPushoutLeftMap_mono A r C
  let _ := presentedPerfectDGKanAssemblyCylinderCompletionUnit_mono A r C
  change Mono ((show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
    ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
      presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r C).right ≫
    (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right)
  infer_instance

/-- 元の右標的から同じ Kan 候補への比較は、基礎単体集合上で単射。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionRightMap_mono (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r C).right := by
  let _ := presentedPerfectDGKanAssemblyCylinderPushoutRightMap_mono A r C
  let _ := presentedPerfectDGKanAssemblyCylinderCompletionUnit_mono A r C
  change Mono ((show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
    ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
      presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C).right ≫
    (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right)
  infer_instance

/-- 元の右標的から同じ Kan 候補への比較は、局所化で可逆。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletionRightMap_localized_isIso (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r C).right) := by
  let _ := presentedPerfectDGKanAssemblyCylinderPushoutRightMap_localized_isIso A r C
  let _ := (Localization.inverts AnodyneHomotopy.anodyneQ anodyneExtensions) _
    (presentedPerfectDGKanAssemblyCylinderCompletionUnit_anodyne A r C)
  change IsIso (AnodyneHomotopy.anodyneQ.map
    ((show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C).right ≫
      (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
        ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
          presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 元の二脚と同じ Kan 候補の両標的比較は、局所化で厳密に可換。 -/
lemma presentedPerfectDGKanAssemblyCylinderCompletion_localized_square (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    AnodyneHomotopy.anodyneQ.map
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyLeftMap A r C).right ≫
        AnodyneHomotopy.anodyneQ.map
          (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
            ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
              presentedPerfectDGKanAssemblyCylinderCompletionLeftMap A r C).right =
      AnodyneHomotopy.anodyneQ.map
        (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj C).obj ⟶
          ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj from
            presentedPerfectDGKanAssemblyRightMap A r C).right ≫
        AnodyneHomotopy.anodyneQ.map
          (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
            ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
              presentedPerfectDGKanAssemblyCylinderCompletionRightMap A r C).right := by
  have h := presentedPerfectDGKanAssemblyCylinderPushout_localized_square A r C
  have hu := congrArg (fun q => q ≫ AnodyneHomotopy.anodyneQ.map
    (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right) h
  have hl := AnodyneHomotopy.anodyneQ.map_comp
    (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r C).right
    (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right
  have hr := AnodyneHomotopy.anodyneQ.map_comp
    (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r C).right
    (show ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj C).obj ⟶
      ((presentedPerfectDGKanAssemblyCylinderCompletionFunctor A r).obj C).obj from
        presentedPerfectDGKanAssemblyCylinderCompletionUnit A r C).right
  erw [hl, hr]
  exact (Category.assoc _ _ _).symm.trans (hu.trans (Category.assoc _ _ _))

end SerrePositivity.KST.SConstruction
