module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberValueMap

/-!
概要：同じ評価余錐の実際の fiber 写像を、元の大域変換の unstraightening の像へ比較する。
方針：変換空間内の構成済み同型を、元の定値標的比較で写す。
規約：native な fiber 写像そのものと同じ全空間・値を保持する。
使われ方：元の始点固定の評価の弱同値性を native 密度余錐へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 元の大域変換の同じ評価を unstraighten して得る、元の値への全空間写像。 -/
def presheafDensityEvaluatedFiberMap :
    leftUnstraightening (presheafDensityEvaluationDiagram F x) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj
        (spaceInfinityObject (presheafDensityEvaluationVertex F x)).obj :=
  (functorVertexEquiv _ _).symm
    ((F2.coherentConstantTargetMap (presheafDensityEvaluationDiagram F x)
      (presheafDensityEvaluationVertex F x)).app (Opposite.op ⦋0⦌)
        (presheafDensityEvaluatedTransformationVertex F x))

/-- 同じ全空間写像の頂点は、元の変換の実際の unstraightening の像そのもの。 -/
lemma presheafDensityEvaluatedFiberMap_vertex :
    functorVertex (presheafDensityEvaluatedFiberMap F x) =
      (F2.coherentConstantTargetMap (presheafDensityEvaluationDiagram F x)
        (presheafDensityEvaluationVertex F x)).app (Opposite.op ⦋0⦌)
          (presheafDensityEvaluatedTransformationVertex F x) :=
  (functorVertexEquiv _ _).apply_symm_apply _

/-- 同じ native 評価余錐の fiber 写像自身は、元の大域変換の同じ像と関手同型。 -/
def presheafDensityEvaluationFiberIso :
    FunctorIso (F2.coconeFiberValueMapAt (presheafDensityEvaluationCocone F x)
      (presheafDensityEvaluationVertex F x) (presheafDensityEvaluationCocone_vertex F x))
      (presheafDensityEvaluatedFiberMap F x) := by
  have hn := F2.coconeFiberValueMapAt_vertex (presheafDensityEvaluationCocone F x)
    (presheafDensityEvaluationVertex F x) (presheafDensityEvaluationCocone_vertex F x)
  have e := VertexIso.map (presheafDensityEvaluationCoconeTransformationIso F x)
    (F2.coherentConstantTargetMap (presheafDensityEvaluationDiagram F x)
      (presheafDensityEvaluationVertex F x))
  exact eqToIso (congrArg HomotopyCategory.mk hn) ≪≫ e ≪≫
    eqToIso (congrArg HomotopyCategory.mk (presheafDensityEvaluatedFiberMap_vertex F x).symm)

end SerrePositivity.InfinityCategories.F2.Ind
