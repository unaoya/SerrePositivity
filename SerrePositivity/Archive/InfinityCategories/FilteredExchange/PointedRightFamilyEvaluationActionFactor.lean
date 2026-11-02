module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyTransportActionFactor
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedTargetFiberTransport

/-!
概要：全右 Hom 比較の評価作用と輸送作用を、元の値比較が使う二つの指定因子で表す。
方針：同じ点同型の評価像を右 fiber へ写し、輸送像を元の普遍終点の像へ戻す。
規約：元の全族・指定値を保つ。使われ方：元の余単位を代入する正方形の直接表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  {x x' : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj} (a : FunctorIso x x')
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K)
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom K L)
local notation "F" => pointedRightFamilyEvaluation (fst A H) (snd A H)
local notation "E" => FiberTransportFamily.endpoint (parametrizedFiberTransportFamily
  pointedSpaceProjection (spaceInfinityVertex K) (spaceInfinityVertex L))

/-- 元の点同型を、同じ動く射で評価した値の指定同型。 -/
def pointedRightFamilyEvaluationValueIso :
    FunctorIso (pointedRightFamilyEvaluation x y) (pointedRightFamilyEvaluation x' y) :=
  functorIsoOfEq ((functorIsoLiftRight a y).postcomp F) (by rfl) (by rfl)

/-- 元の指定評価作用は、同じ値の指定評価像を右 fiber へ写した同型に厳密に等しい。 -/
lemma pointedRightFamilyEvaluationActionIso_eq_value :
    pointedRightFamilyEvaluationActionIso a y =
      (pointedRightFamilyEvaluationValueIso a y).postcomp (pointedRightFiberComparison L) := by
  have hp := functorIsoOfEq_heq ((functorIsoLiftRight a y).postcomp
    (F ≫ pointedRightFiberComparison L))
    (pointedRightFamilyUniversal_source x y) (pointedRightFamilyUniversal_source x' y)
  have hv := functorIsoOfEq_postcomp_heq ((functorIsoLiftRight a y).postcomp F)
    (show lift x y ≫ F = pointedRightFamilyEvaluation x y by rfl)
    (show lift x' y ≫ F = pointedRightFamilyEvaluation x' y by rfl)
    (pointedRightFiberComparison L)
  exact eq_of_heq (hp.trans
    ((heq_of_eq (functorIso_postcomp_postcomp (functorIsoLiftRight a y) F
      (pointedRightFiberComparison L))).symm.trans hv.symm))

/-- 同じ全右 Hom 比較の正方形を、値の評価像と元の始点同型の普遍終点像で直接表す。 -/
lemma pointedRightFamilyTransportIso_source_square :
    (pointedRightFamilyEvaluationValueIso a y).postcomp (pointedRightFiberComparison L) ≪≫
        pointedRightFamilyTransportIso x' y =
      pointedRightFamilyTransportIso x y ≪≫
        (functorIsoLiftRight (a.postcomp (pointedRightFiberComparison K))
          (y ≫ coherentKanRightHomInterval K L)).postcomp E := by
  have h := pointedRightFamilyTransportIso_action_square a y
  rw [pointedRightFamilyEvaluationActionIso_eq_value] at h
  have ht := eq_of_heq (pointedRightFamilyTransportActionIso_heq_source a y)
  rw [ht] at h
  exact h

end SerrePositivity.InfinityCategories.F2
