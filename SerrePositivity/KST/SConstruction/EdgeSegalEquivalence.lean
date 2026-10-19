module
public import SerrePositivity.KST.SConstruction.EdgeSegalEvaluations
public import SerrePositivity.KST.SConstruction.NonemptySSetPowers

/-! # 全連続辺への Segal 射の正の反復実現後の同値
概要：元の各辺評価から作る S_n C の Segal 射が全正有限反復実現で局所化同型となる。
方針：最初の辺での切断と残りの全辺評価との厳密な分解式を証明し、二分割同値で帰納する。
規約：正の辺数を扱い、元の各成分の式を明示する。使われ方：経路面の引き戻し条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 元の全連続辺への評価を束ねた正の反復実現の Segal 射。 -/
def edgeSegalMap (r n : ℕ) (X : StableModel.{u}) :
    (multiRealizationFunctor (r + 1)).obj (sStableModel (n + 1) X) ⟶
      nonemptySSetPower ((multiRealizationFunctor (r + 1)).obj (sStableModel 1 X)) n :=
  nonemptySSetPowerLift n (fun i =>
    (multiRealizationFunctor (r + 1)).map (edgeSegalEvaluation (n + 1) i X))

/-- 全辺 Segal 射の i 番目の成分は元の i 番目の連続辺への評価。 -/
lemma edgeSegalMap_projection (r n : ℕ) (X : StableModel.{u}) (i : Fin (n + 1)) :
    edgeSegalMap r n X ≫
        nonemptySSetPowerProjection
          ((multiRealizationFunctor (r + 1)).obj (sStableModel 1 X)) n i =
      (multiRealizationFunctor (r + 1)).map (edgeSegalEvaluation (n + 1) i X) :=
  nonemptySSetPowerLift_projection n _ i

/-- 一辺の Segal 射は元の恒等射。 -/
lemma edgeSegalMap_zero (r : ℕ) (X : StableModel.{u}) :
    edgeSegalMap r 0 X = 𝟙 _ := by
  change (multiRealizationFunctor (r + 1)).map (edgeSegalEvaluation 1 0 X) = _
  rw [edgeSegalEvaluation_one, CategoryTheory.Functor.map_id]

/-- 元の全辺 Segal 射は最初の辺での切断と残りの全辺評価に厳密に分解する。 -/
lemma edgeSegalMap_succ (r n : ℕ) (X : StableModel.{u}) :
    edgeSegalMap r (n + 1) X = cutSegalMap r (n + 2) ⟨1, by omega⟩ X ≫
      (𝟙 _ ⊗ₘ edgeSegalMap r n X) := by
  let F := multiRealizationFunctor (r + 1)
  change CartesianMonoidalCategory.lift _ _ = CartesianMonoidalCategory.lift _ _ ≫ (_ ⊗ₘ _)
  rw [CartesianMonoidalCategory.lift_map, Category.comp_id, cutLeftSegalEvaluation_first]
  congr 1
  change nonemptySSetPowerLift n _ = F.map (cutRightSegalEvaluation _ _ X) ≫
    nonemptySSetPowerLift n _
  rw [nonemptySSetPowerLift_comp]
  congr 1
  funext i
  rw [← F.map_comp, cutRightSegalEvaluation_edge]

/-- 元の全辺 Segal 射は全正有限反復 core S• 実現で局所化同型。 -/
lemma edgeSegalMap_localized_isIso (r n : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (edgeSegalMap r n X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  induction n with
  | zero => rw [edgeSegalMap_zero, Q.map_id]; infer_instance
  | succ n ih =>
    have hC := cutSegalMap_localized_isIso r (n + 2) ⟨1, by omega⟩ X
    have hW := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso (edgeSegalMap r n X) ih
      ((multiRealizationFunctor (r + 1)).obj (sStableModel 1 X))
    rw [edgeSegalMap_succ, Q.map_comp, id_tensorHom]
    infer_instance

end SerrePositivity.KST.SConstruction
