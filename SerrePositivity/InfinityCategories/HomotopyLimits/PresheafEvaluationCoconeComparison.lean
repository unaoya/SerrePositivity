module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafCoherentColimitCones
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Stable.CoconeFamily

/-!
概要：前層圏の指定余錐の各評価を、元の標準全空間余極限余錐へ比較する。
方針：同じ coslice 内の始対象の一意性から、頂点と元の全余錐への作用を取る。
規約：元の指定余錐と評価点を保持。底の quasicategory 性や sifted 性は不要。
使われ方：前層余極限頂点の元の有限錐像と、全評価 Kan 脚の標準錐の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C)
  (q : JoinCocone r)
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  (x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌)

/-- 同じ評価図式上の元の評価余極限余錐と標準全空間余錐の、同じ coslice 内の比較。 -/
def presheafEvaluationCoconeIso :
    VertexIso (X := sliceUnder (r ≫ evaluateFunctorAt x))
      (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q)
      (F2.coherentDiagramTotalCocone (r ≫ evaluateFunctorAt x)) :=
  initialVertexIso (hq x) (F2.coherentDiagramTotalCocone_isColimit _)

/-- 同じ coslice 比較を頂点に写すと、元の評価頂点と標準余極限頂点の同型になる。 -/
def presheafEvaluationColimitVertexIso :
    VertexIso (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q).vertex
      (F2.coherentDiagramTotalVertex (r ≫ evaluateFunctorAt x)) := by
  have e := (presheafEvaluationCoconeIso r q hq x).map
    (sliceUnderProjection (r ≫ evaluateFunctorAt x))
  change VertexIso (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q).vertex
    (F2.coherentDiagramTotalCocone (r ≫ evaluateFunctorAt x)).vertex at e
  rw [F2.coherentDiagramTotalCocone_vertex] at e
  exact e

/-- 同じ coslice 比較は、元の全評価余錐の射と標準全余錐の射の間の関手同型を与える。 -/
def presheafEvaluationWholeCoconeIso :
    FunctorIso (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q).val
      (F2.coherentDiagramTotalCocone (r ≫ evaluateFunctorAt x)).val := by
  let D := r ≫ evaluateFunctorAt x
  have e := (presheafEvaluationCoconeIso r q hq x).map
    (cosliceCoconeFamilyMap D ≫ vertexFiberι (coconeRestriction _ _) (functorVertex D))
  change VertexIso
    ((cosliceCoconeFamilyMap D).app _ (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q)).val
    ((cosliceCoconeFamilyMap D).app _ (F2.coherentDiagramTotalCocone D)).val at e
  rw [cosliceCoconeFamilyMap_app_zero, cosliceCoconeFamilyMap_app_zero] at e
  exact e

end SerrePositivity.InfinityCategories.HomotopyLimits
