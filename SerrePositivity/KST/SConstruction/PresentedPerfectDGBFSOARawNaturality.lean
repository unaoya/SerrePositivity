module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSOAComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFRealizationInvariance
public import SerrePositivity.KST.SConstruction.PointedComponentNaturalSquare
public import SerrePositivity.KST.Spectra.PointedCurryingParameterComponents

/-! # 元の SOA K 候補列と新 BF 列の全段比較の入力自然性
概要：全段の同じ前向き比較は、元の通常 dg 入力射と点つき成分で可換。
方針：元の二 Kan 模型の比較自然性を、loop と厳密な前向き段比較へ移す。
規約：入力の実 BF 射は変更しない。使われ方：整数 π・π₀ 比較の自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の境界商の SOA・Ex∞ 比較は、元の通常 dg 射に成分で自然。 -/
lemma presentedPerfectDGBFBoundarySOAComparison_naturality_component
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (r : ℕ) :
    componentOf (presentedPerfectDGBFBoundarySOAComparison A r X ≫
        (presentedPerfectDGBoundaryKanMap A r f).hom) =
      componentOf ((boundaryKanRealizationFunctor r).map (presentedPerfectDGBFInputStableMap A f) ≫
        presentedPerfectDGBFBoundarySOAComparison A r Y) :=
  pointedSOAExInfinityComparison_naturality_component
    (presentedPerfectDGBoundaryPointedMap A r f)

/-- 全ての正段の同じ前向き比較は、元の通常 dg 射に成分で自然。 -/
lemma presentedPerfectDGBFRawSOAComparison_positive_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (r : ℕ) :
    componentOf (kKanSequenceLevelMap (presentedPerfectDGBFInputStableMap A f) (r + 1) ≫
        presentedPerfectDGBFRawSOAComparison A Y (r + 1)) =
      componentOf (presentedPerfectDGBFRawSOAComparison A X (r + 1) ≫
        (presentedPerfectDGBFMap A f).app (r + 1)) := by
  let S := presentedPerfectDGBFPositiveStage A r
  have h := pointedComponentNaturalSquare_post
    ((boundaryKanRealizationFunctor r).map (presentedPerfectDGBFInputStableMap A f))
    (presentedPerfectDGBoundaryKanMap A r f).hom
    (presentedPerfectDGBFBoundarySOAComparison A r X)
    (presentedPerfectDGBFBoundarySOAComparison A r Y)
    (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶
      (S.functor.obj X).obj from S.comparison X)
    (show ((presentedPerfectDGBFBoundaryFunctor A r).obj Y).obj ⟶
      (S.functor.obj Y).obj from S.comparison Y)
    (show (S.functor.obj X).obj ⟶ (S.functor.obj Y).obj from
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap S.functor f)
    (presentedPerfectDGBFBoundarySOAComparison_naturality_component A f r)
    (presentedPerfectDGBFStageComparison_naturality A r S f)
  erw [presentedPerfectDGBFMap_positive_app A f r]
  exact h

/-- 零段の同じ loop 比較は、元の通常 dg 射に成分で自然。 -/
lemma presentedPerfectDGBFRawSOAComparison_zero_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    componentOf (kKanSequenceLevelMap (presentedPerfectDGBFInputStableMap A f) 0 ≫
        presentedPerfectDGBFRawSOAComparison A Y 0) =
      componentOf (presentedPerfectDGBFRawSOAComparison A X 0 ≫
        (presentedPerfectDGBFMap A f).app 0) := by
  let L := PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}
  have h := componentOf_ihom_map PointedSimplicialSet.circle.{max (u + 1) v}
    (presentedPerfectDGBFBoundarySOAComparison_naturality_component A f 0)
  rw [presentedPerfectDGBFMap_zero_app]
  exact (congrArg componentOf (L.map_comp
    ((boundaryKanRealizationFunctor 0).map (presentedPerfectDGBFInputStableMap A f))
    (presentedPerfectDGBFBoundarySOAComparison A 0 Y)).symm).trans
    (h.symm.trans (congrArg componentOf (L.map_comp
      (presentedPerfectDGBFBoundarySOAComparison A 0 X)
      (presentedPerfectDGBoundaryKanMap A 0 f).hom)))

/-- 同じ元の K 候補列から新 BF 列への全段比較は、全入力射に成分で自然。 -/
lemma presentedPerfectDGBFRawSOAComparison_naturality
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) (n : ℕ) :
    componentOf (kKanSequenceLevelMap (presentedPerfectDGBFInputStableMap A f) n ≫
        presentedPerfectDGBFRawSOAComparison A Y n) =
      componentOf (presentedPerfectDGBFRawSOAComparison A X n ≫
        (presentedPerfectDGBFMap A f).app n) := by
  cases n with
  | zero => exact presentedPerfectDGBFRawSOAComparison_zero_naturality A f
  | succ r => exact presentedPerfectDGBFRawSOAComparison_positive_naturality A f r

end SerrePositivity.KST.SConstruction
