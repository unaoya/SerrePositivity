module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityCoconeTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：同じ native 密度余錐を各対象で評価し、その標準変換を同じ大域変換の評価へ比較する。
方針：標準変換の後合成自然性と、両端固定実現からの変換同型を組み合わせる。
規約：余錐・図式・指定頂点は元の評価で写したものを使う。
使われ方：余錐の fiber 写像を証明済みの始点固定の大域評価へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 同じ密度図式を、指定した対象で評価した図式。 -/
def presheafDensityEvaluationDiagram :=
  presheafElementsYonedaDiagram F ≫ presheafInfinityEvaluation x

/-- 同じ評価の指定頂点。 -/
def presheafDensityEvaluationVertex :=
  (presheafInfinityEvaluation x).app (Opposite.op ⦋0⦌) (functorVertex F)

omit [Quasicategory C] in
/-- 評価した指定頂点は、元の前層の同じ対象での値そのもの。 -/
lemma presheafDensityEvaluationVertex_value : presheafDensityEvaluationVertex F x =
    F.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x)) :=
  evaluateFunctorAt_functorVertex _ _

/-- 同じ密度余錐を元の評価で写した native な余錐。 -/
def presheafDensityEvaluationCocone : JoinCocone (presheafDensityEvaluationDiagram F x) :=
  mapJoinCocone (presheafInfinityEvaluation x) (presheafDensityCocone F)

/-- 同じ評価した余錐の頂点は元の指定頂点の評価。 -/
lemma presheafDensityEvaluationCocone_vertex :
    (presheafDensityEvaluationCocone F x).vertex = presheafDensityEvaluationVertex F x := by
  rw [presheafDensityEvaluationCocone, mapJoinCocone_vertex, presheafDensityCocone_vertex]
  rfl

/-- 同じ評価した native 余錐が定める標準変換の指定頂点。 -/
def presheafDensityEvaluationCoconeTransformationVertex :=
  (F2.coconeTransformationMap (presheafDensityEvaluationDiagram F x)
    (presheafDensityEvaluationVertex F x)).app (Opposite.op ⦋0⦌)
      (F2.coconeMappingPointAt (presheafDensityEvaluationCocone F x)
        (presheafDensityEvaluationVertex F x) (presheafDensityEvaluationCocone_vertex F x))

/-- 同じ元の大域密度変換を評価した指定変換頂点。 -/
def presheafDensityEvaluatedTransformationVertex :=
  (F2.constantTransformationPost (presheafElementsYonedaDiagram F) (functorVertex F)
    (presheafInfinityEvaluation x)).app (Opposite.op ⦋0⦌) (presheafDensityTransformationVertex F)

/-- 同じ評価余錐の標準変換は、元の大域変換の同じ評価と同型。 -/
def presheafDensityEvaluationCoconeTransformationIso :
    VertexIso (presheafDensityEvaluationCoconeTransformationVertex F x)
      (presheafDensityEvaluatedTransformationVertex F x) := by
  have h := coconeTransformationPointAt_post (presheafDensityCocone F) (functorVertex F)
    (presheafDensityCocone_vertex F) (presheafInfinityEvaluation x)
      (presheafDensityEvaluationCocone_vertex F x)
  exact eqToIso (congrArg HomotopyCategory.mk h.symm) ≪≫
    VertexIso.map (presheafDensityCoconeTransformationIso F)
      (F2.constantTransformationPost (presheafElementsYonedaDiagram F) (functorVertex F)
        (presheafInfinityEvaluation x))

end SerrePositivity.InfinityCategories.F2.Ind
