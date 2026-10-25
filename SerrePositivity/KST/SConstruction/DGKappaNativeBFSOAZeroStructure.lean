module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFSOAComparison
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderComponents

/-! # 元の SOA K 列と新 BF 列の零構造射の比較
概要：前向き零段・第一段比較は、同じ元の評価と実円柱を点つき成分で結ぶ。
方針：元の評価の自然性と、同じ最初の円柱源射の成分を使う。
規約：列全体の厳密比較は別工程。使われ方：元の K との比較の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open DifferentialGraded NonConnective Fibration
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open Spectra.PointedMapping SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ元の K 候補列と新 BF 列の零構造射は、前向き比較で点つき成分が可換。
方針：同じ実段比較と元の単射構造射を使う。
規約：同じ有限 native 入力に限定。使われ方：二頂点の実スペクトル比較。 -/
lemma dgKappaNativeBFRawSOAComparison_zero_structure (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    componentOf
        (PointedSimplicialSet.circle.{max (u + 1) v} ◁
            dgKappaNativeBFRawSOAComparison.{u, v} R D I C 0 ≫
          (dgKappaNativeBFFiniteOmegaSpectrum.{u, v} R D I C).sigma 0) =
      componentOf
        ((kKanSequence (sInputModel C.obj)).sigma 0 ≫
          dgKappaNativeBFRawSOAComparison.{u, v} R D I C 1) := by
  let b := dgKappaNativeBFBoundarySOAComparison.{u, v} R D I 0 C
  let j : ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0).obj C).obj ⟶
      ((dgKappaNativeBFFiniteFirstFunctor.{u, v} R D I).obj C).obj :=
    dgKappaNativeBFFiniteFirstComparison.{u, v} R D I C
  have h := componentOf_comp_left
    (pointedEnrichedMonicReplacementSource_component
      (dgKappaNativeBFFiniteZeroSuspensionFunctor.{u, v} R D I)
      (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I 0)
      (dgKappaNativeBFFiniteZeroEvaluation.{u, v} R D I)
      (dgKappaNativeBFFiniteZeroEvaluation_whisker.{u, v} R D I) C)
    (PointedSimplicialSet.circle.{max (u + 1) v} ◁
      (PointedObject.basedHomFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map b)
  refine h.trans ?_
  apply congrArg componentOf
  change (PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (ihom PointedSimplicialSet.circle.{max (u + 1) v}).map b) ≫
      ((ihom.ev PointedSimplicialSet.circle.{max (u + 1) v}).app _ ≫ j) = _
  erw [← Category.assoc, ihom.ev_naturality, Category.assoc]
  change (ihom.ev PointedSimplicialSet.circle.{max (u + 1) v}).app _ ≫ b ≫ j =
    uncurry (𝟙 _) ≫ (b ≫ j)
  rw [uncurry_id_eq_ev]
  rfl

end SerrePositivity.KST.SConstruction
