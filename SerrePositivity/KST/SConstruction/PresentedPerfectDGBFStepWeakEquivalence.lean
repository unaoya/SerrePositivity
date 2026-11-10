module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepProperties
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyLeftEquivalence
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison

/-! # 実際の BF 帰納段における前向き弱比較の保存
概要：Bᵣ→K が Kan 値間の弱比較なら、同じ次段 B_(r+1)→K' も弱比較。
方針：元の比較の全基点 π 同型から suspension の弱比較を得て、同じ左脚を合成する。
規約：ΣEx∞→Ex∞Σ の単射性・弱同値性は仮定しない。使われ方：正の全帰納列。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

variable (r : ℕ)
  (K : EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
    PointedSSetObject.{max (u + 1) v})
  (c : ∀ X, (presentedPerfectDGBFBoundaryFunctor A r).obj X ⟶ K.obj X)
  (hc : ∀ X Y, (presentedPerfectDGBFBoundaryFunctor A r).map X Y ≫
      eHomWhiskerLeft SSet ((presentedPerfectDGBFBoundaryFunctor A r).obj X) (c Y) =
    K.map X Y ≫ eHomWhiskerRight SSet (c X) (K.obj Y))

open SerrePositivity.SimplicialModel

/-- 元の Kan 値間の弱比較を suspension した同じ射も局所化可逆。 -/
lemma presentedPerfectDGBFStepSuspensionComparison_localized_isIso
    (X : PerfDGInput.{u, v} A) (hK : KanComplex (K.obj X).obj.right)
    (hcmp : IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶ (K.obj X).obj from
        c X).right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X).obj ⟶
        ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj X).obj from
          presentedPerfectDGBFStepSuspensionComparison A r K c X).right) := by
  let _ := hK
  let _ : KanComplex (((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  let a : ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶ (K.obj X).obj := c X
  have hp := kanPiIsomorphism_of_localized_isIso a.right hcmp
  exact suspensionImage_isIso_of_piIsomorphism AnodyneHomotopy.anodyneQ
    (Localization.inverts _ anodyneExtensions) a hp

/-- 実際の ΣK へ延長した元の左脚は、元の前向き弱比較から局所化可逆。 -/
lemma presentedPerfectDGBFStepLeftMap_localized_isIso
    (X : PerfDGInput.{u, v} A) (hK : KanComplex (K.obj X).obj.right)
    (hcmp : IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶ (K.obj X).obj from
        c X).right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblySourceFunctor A r).obj X).obj ⟶
        ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj X).obj from
          presentedPerfectDGBFStepLeftMap A r K c X).right) := by
  let a : ((presentedPerfectDGKanAssemblySourceFunctor A r).obj X).obj ⟶
      ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X).obj :=
    presentedPerfectDGKanAssemblyLeftMap A r X
  let b : ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X).obj ⟶
      ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj X).obj :=
    presentedPerfectDGBFStepSuspensionComparison A r K c X
  let _ : IsIso (AnodyneHomotopy.anodyneQ.map a.right) :=
    presentedPerfectDGKanAssemblyLeftMap_localized_isIso A r X
  let _ : IsIso (AnodyneHomotopy.anodyneQ.map b.right) :=
    presentedPerfectDGBFStepSuspensionComparison_localized_isIso A r K c X hK hcmp
  change IsIso (AnodyneHomotopy.anodyneQ.map (a.right ≫ b.right))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 同じ次段への元の右標的比較は、Kan 性と前向き弱比較を保持する。 -/
lemma presentedPerfectDGBFStepComparison_localized_isIso
    (X : PerfDGInput.{u, v} A) (hK : KanComplex (K.obj X).obj.right)
    (hcmp : IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶ (K.obj X).obj from
        c X).right)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj X).obj ⟶
        ((presentedPerfectDGBFStepFunctor A r K c hc).obj X).obj from
          presentedPerfectDGBFStepComparison A r K c hc X).right) :=
  pointedEnrichedCylinderCompletionRight_localized_isIso
    (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r)
    X (presentedPerfectDGBFStepLeftMap_localized_isIso A r K c X hK hcmp)

end SerrePositivity.KST.SConstruction
