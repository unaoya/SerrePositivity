module
public import SerrePositivity.KST.SConstruction.CutSegalEquivalence

/-! # 切断 Segal 同値の入力についての自然性
概要：元の二区間制限の Segal 射を完全関手に関して自然な局所化同型に束ねる。
方針：S の単体作用の自然性を二成分で実現し、成分ごとの可逆性を適用する。
規約：自然同型の成分は元の Segal 射の像。使われ方：経路面と K の関手性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 任意の実現関手の下で元の二区間制限の射対は入力について厳密に自然。 -/
lemma cutSegalPair_naturality (F : StableModel.{u} ⥤ SSet.{u}) (n : ℕ)
    (k : Fin (n + 1)) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    F.map ((sEndofunctor n).map f) ≫
      CartesianMonoidalCategory.lift (F.map (cutLeftSegalEvaluation n k Y))
        (F.map (cutRightSegalEvaluation n k Y)) =
    CartesianMonoidalCategory.lift (F.map (cutLeftSegalEvaluation n k X))
      (F.map (cutRightSegalEvaluation n k X)) ≫
        (F.map ((sEndofunctor k.val).map f) ⊗ₘ
          F.map ((sEndofunctor (n - k.val)).map f)) := by
  have hL := (sEndofunctorMap (cutLeftIntervalInclusion n k)).naturality f
  have hR := (sEndofunctorMap (cutRightIntervalInclusion n k)).naturality f
  change (sEndofunctor n).map f ≫ cutLeftSegalEvaluation n k Y =
    cutLeftSegalEvaluation n k X ≫ (sEndofunctor k.val).map f at hL
  change (sEndofunctor n).map f ≫ cutRightSegalEvaluation n k Y =
    cutRightSegalEvaluation n k X ≫ (sEndofunctor (n - k.val)).map f at hR
  rw [CartesianMonoidalCategory.comp_lift, CartesianMonoidalCategory.lift_map,
    ← F.map_comp, ← F.map_comp, hL, hR, F.map_comp, F.map_comp]

/-- 正の反復実現の切断 Segal 射を元の入力上の自然変換に束ねる。 -/
def cutSegalNat (r n : ℕ) (k : Fin (n + 1)) :
    sEndofunctor.{u} n ⋙ multiRealizationFunctor (r + 1) ⟶
      (sEndofunctor k.val ⋙ multiRealizationFunctor (r + 1)) ⊗
        (sEndofunctor (n - k.val) ⋙ multiRealizationFunctor (r + 1)) where
  app X := cutSegalMap r n k X
  naturality {_X _Y} f := cutSegalPair_naturality (multiRealizationFunctor (r + 1)) n k f

/-- 任意の切断位置の正の反復 Segal 射は局所化後に完全関手について自然な同型。 -/
def cutSegalLocalizedIso (r n : ℕ) (k : Fin (n + 1)) :
    sEndofunctor.{u} n ⋙ multiRealizationFunctor (r + 1) ⋙ AnodyneHomotopy.anodyneQ ≅
      ((sEndofunctor k.val ⋙ multiRealizationFunctor (r + 1)) ⊗
        (sEndofunctor (n - k.val) ⋙ multiRealizationFunctor (r + 1))) ⋙
          AnodyneHomotopy.anodyneQ := by
  let η := Functor.whiskerRight (cutSegalNat r n k) AnodyneHomotopy.anodyneQ
  have (X : StableModel.{u}) : IsIso (η.app X) := cutSegalMap_localized_isIso r n k X
  have : IsIso η := NatIso.isIso_of_isIso_app _
  exact asIso η

/-- 局所化した自然同型の成分は元の区間制限の Segal 射そのものの像。 -/
lemma cutSegalLocalizedIso_app (r n : ℕ) (k : Fin (n + 1)) (X : StableModel.{u}) :
    (cutSegalLocalizedIso r n k).hom.app X =
      AnodyneHomotopy.anodyneQ.map (cutSegalMap r n k X) := rfl

end SerrePositivity.KST.SConstruction
