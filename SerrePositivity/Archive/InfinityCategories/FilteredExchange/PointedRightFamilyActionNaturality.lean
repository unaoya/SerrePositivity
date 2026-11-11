module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyUniversalComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyUniversalEndpoints
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPair
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoSquareValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatTensorAndArrowObjects

/-!
概要：動く点の指定同型に関し、元の全右 Hom 比較が同じ指定正方形を満たす。
方針：同じ全直積の指定比較の自然性を、元の四実端点へ表示変更する。
規約：同じ点同型・動く射と指定比較を保持。使われ方：単位・余単位を介する値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  {x x' : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj} (a : FunctorIso x x')
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K)
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom K L)
local notation "M" => pointedRightFamilyEvaluation (fst A H) (snd A H) ≫
  pointedRightFiberComparison L
local notation "N" => diagonalFiberTransport pointedSpaceProjection
  (fst A H ≫ pointedRightFiberComparison K) (snd A H ≫ coherentKanRightHomInterval K L)
local notation "U" => pointedRightFamilyTransportIso (fst A H) (snd A H)

/-- 元の点同型を、同じ全直積の評価と右 fiber 比較で写した指定同型。 -/
def pointedRightFamilyEvaluationActionIso :
    FunctorIso (pointedRightFamilyEvaluation x y ≫ pointedRightFiberComparison L)
      (pointedRightFamilyEvaluation x' y ≫ pointedRightFiberComparison L) :=
  functorIsoOfEq ((functorIsoLiftRight a y).postcomp M)
    (pointedRightFamilyUniversal_source x y) (pointedRightFamilyUniversal_source x' y)

/-- 元の点同型を、同じ全直積の輸送で写した指定同型。 -/
def pointedRightFamilyTransportActionIso :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection (x ≫ pointedRightFiberComparison K)
        (y ≫ coherentKanRightHomInterval K L))
      (diagonalFiberTransport pointedSpaceProjection (x' ≫ pointedRightFiberComparison K)
        (y ≫ coherentKanRightHomInterval K L)) :=
  functorIsoOfEq ((functorIsoLiftRight a y).postcomp N)
    (pointedRightFamilyUniversal_target x y) (pointedRightFamilyUniversal_target x' y)

/-- 元の動く点同型と同じ射の全族で、同じ右 Hom 指定比較の正方形は可換である。 -/
lemma pointedRightFamilyTransportIso_action_square :
    pointedRightFamilyEvaluationActionIso a y ≪≫ pointedRightFamilyTransportIso x' y =
      pointedRightFamilyTransportIso x y ≪≫ pointedRightFamilyTransportActionIso a y := by
  have : Quasicategory (A ⊗ H) := quasicategory_tensor A H
  exact functorIso_square_of_heq
    ((functorIsoLiftRight a y).postcomp M) (FunctorIso.precomp U (lift x' y))
    (FunctorIso.precomp U (lift x y)) ((functorIsoLiftRight a y).postcomp N)
    (pointedRightFamilyEvaluationActionIso a y) (pointedRightFamilyTransportIso x' y)
    (pointedRightFamilyTransportIso x y) (pointedRightFamilyTransportActionIso a y)
    (pointedRightFamilyUniversal_source x y) (pointedRightFamilyUniversal_source x' y)
    (pointedRightFamilyUniversal_target x y) (pointedRightFamilyUniversal_target x' y)
    (functorIsoOfEq_heq _ _ _) (pointedRightFamilyTransportIso_heq_universal x' y)
    (pointedRightFamilyTransportIso_heq_universal x y) (functorIsoOfEq_heq _ _ _)
    (functorIso_whisker_exchange (functorIsoLiftRight a y) U)

end SerrePositivity.InfinityCategories.F2
