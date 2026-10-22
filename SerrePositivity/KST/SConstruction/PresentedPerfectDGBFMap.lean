module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFEnrichedFunctor

/-! # 厳密 dg 関手の同じ実 BF 射と各段の回収
概要：実 BF 豊穣関手から通常の dg 関手に対応する厳密スペクトル射を取り出す。
方針：標準豊穣 Hom の同値と写像塔の各段評価を使う。
規約：元の全高次入力作用を保つ。使われ方：元の dgK 射との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 通常射との同値も同じ実 BF 単体的圏のものを使う。 -/
local instance presentedPerfectDGBFMapTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 厳密 dg 関手に対応する同じ実 BF スペクトルの厳密な射。 -/
def presentedPerfectDGBFMap {X Y : PerfDGInput.{u, v} A} (F : X ⟶ Y) :
    presentedPerfectDGBFOmegaSpectrum A X ⟶ presentedPerfectDGBFOmegaSpectrum A Y :=
  (eHomEquiv SSet).symm (eHomEquiv SSet F ≫ (presentedPerfectDGBFEnrichedFunctor A).map X Y)

/-- 元の通常 dg 射を豊穣 Hom へ写すと、同じ実 BF 射の表示を回収する。 -/
lemma presentedPerfectDGBFMap_hom {X Y : PerfDGInput.{u, v} A} (F : X ⟶ Y) :
    eHomEquiv SSet (presentedPerfectDGBFMap A F) =
      eHomEquiv SSet F ≫ (presentedPerfectDGBFEnrichedFunctor A).map X Y :=
  Equiv.apply_symm_apply _ _

/-- 同じ厳密 BF 射は、各段で元の厳密豊穣作用による通常射を回収する。 -/
lemma presentedPerfectDGBFMap_app {X Y : PerfDGInput.{u, v} A} (F : X ⟶ Y) (n : ℕ) :
    (presentedPerfectDGBFMap A F).app n =
      (show ((presentedPerfectDGBFLevelFunctor A n).obj X).obj ⟶
        ((presentedPerfectDGBFLevelFunctor A n).obj Y).obj from
          (eHomEquiv SSet (X := (presentedPerfectDGBFLevelFunctor A n).obj X)
            (Y := (presentedPerfectDGBFLevelFunctor A n).obj Y)).symm
            (eHomEquiv SSet F ≫ (presentedPerfectDGBFLevelFunctor A n).map X Y)) := by
  let : SimplicialCategory PointedSimplicialSet.{max (u + 1) v} :=
    PointedEnrichment.simplicialCategory
  apply (eHomEquiv SSet).injective
  have h := congrArg (fun k => k ≫ OmegaSpectrum.evaluation
    (presentedPerfectDGBFOmegaSpectrum A X) (presentedPerfectDGBFOmegaSpectrum A Y) n)
    (presentedPerfectDGBFMap_hom A F)
  have hv : eHomEquiv SSet (presentedPerfectDGBFMap A F) =
      OmegaSpectrum.vertexOfHomMap (presentedPerfectDGBFMap A F) := by
    change (SSet.unitHomEquiv _).symm
      ((SSet.unitHomEquiv _) (OmegaSpectrum.vertexOfHomMap (presentedPerfectDGBFMap A F))) = _
    exact Equiv.symm_apply_apply _ _
  erw [hv, OmegaSpectrum.vertexOfHomMap_evaluation, Category.assoc,
    presentedPerfectDGBFEnrichedFunctor_evaluation] at h
  exact h.trans (Equiv.apply_symm_apply _ _).symm

end SerrePositivity.KST.SConstruction
