module
public import SerrePositivity.KST.SConstruction.MultiRealizationEquivalence
public import SerrePositivity.KST.SConstruction.CutStableEquivalences
public import SerrePositivity.KST.SConstruction.CutSegalEvaluations

/-! # 元の切断 Segal 射の反復実現後の同値
概要：任意の切断位置の二区間制限は全正有限反復 core S• 実現後に局所化同型となる。
方針：相対切断の同値・相対加法性・左右支持の区間同値を厳密な射対の式で合成する。
規約：元の制限写像そのものについて証明する。使われ方：連続区間分解と経路面の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 正の反復実現の左右の短い区間への制限の積は局所化同型。 -/
lemma cutIntervalRestrictions_tensor_localized_isIso (r n : ℕ) (k : Fin (n + 1))
    (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (cutLeftIntervalRestriction n k X) ⊗ₘ
        (multiRealizationFunctor (r + 1)).map (cutRightIntervalRestriction n k X))) := by
  let F := multiRealizationFunctor (r + 1)
  have hL := multiRealization_map_localized_isIso_of_equivalence r
    (cutLeftIntervalStableEquivalence n k X)
  have hR := multiRealization_map_localized_isIso_of_equivalence r
    (cutRightIntervalStableEquivalence n k X)
  have h₁ := AnodyneHomotopy.whiskerRight_anodyneQ_isIso
    (F.map (cutLeftIntervalRestriction n k X)) hL
    (F.obj (closedStableModel (cutRightSupport n k X)))
  have h₂ := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso
    (F.map (cutRightIntervalRestriction n k X)) hR (F.obj (sStableModel k.val X))
  rw [tensorHom_def, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- 元の二つの連続区間制限から作る正の反復実現の Segal 射。 -/
def cutSegalMap (r n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    (multiRealizationFunctor (r + 1)).obj (sStableModel n X) ⟶
      (multiRealizationFunctor (r + 1)).obj (sStableModel k.val X) ⊗
        (multiRealizationFunctor (r + 1)).obj (sStableModel (n - k.val) X) :=
  CartesianMonoidalCategory.lift
    ((multiRealizationFunctor (r + 1)).map (cutLeftSegalEvaluation n k X))
    ((multiRealizationFunctor (r + 1)).map (cutRightSegalEvaluation n k X))

/-- 元の切断 Segal 射は全正有限反復 core S• 実現後に局所化同型。 -/
lemma cutSegalMap_localized_isIso (r n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (cutSegalMap r n k X)) := by
  let F := multiRealizationFunctor (r + 1)
  let Q := AnodyneHomotopy.anodyneQ
  have hC := multiRealization_map_localized_isIso_of_equivalence r
    (cutRelativeStableEquivalence n k X)
  change IsIso (Q.map (F.map (cutRelativeComparison n k X))) at hC
  have hA := relativeMultiRealizationAdditivityMap_localized_isIso r
    (cutLeftSupport n k X) (cutRightSupport n k X)
  have hI := cutIntervalRestrictions_tensor_localized_isIso r n k X
  have hi : IsIso (Q.map (F.map (cutRelativeComparison n k X) ≫
      relativeMultiRealizationAdditivityMap (r + 1)
        (cutLeftSupport n k X) (cutRightSupport n k X) ≫
      (F.map (cutLeftIntervalRestriction n k X) ⊗ₘ
        F.map (cutRightIntervalRestriction n k X)))) := by
    rw [Q.map_comp, Q.map_comp]
    infer_instance
  change IsIso (Q.map (F.map (cutRelativeComparison n k X) ≫
    CartesianMonoidalCategory.lift
      (F.map (relativeCofiberSubobject (cutLeftSupport n k X) (cutRightSupport n k X)))
      (F.map (relativeCofiberQuotient (cutLeftSupport n k X) (cutRightSupport n k X))) ≫
    (F.map (cutLeftIntervalRestriction n k X) ⊗ₘ F.map (cutRightIntervalRestriction n k X)))) at hi
  rw [cutRelativeSegalPair] at hi
  exact hi

end SerrePositivity.KST.SConstruction
