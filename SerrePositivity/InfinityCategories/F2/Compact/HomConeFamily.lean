module

public import SerrePositivity.InfinityCategories.F2.Compact.FlipEvaluation
public import SerrePositivity.InfinityCategories.F2.Compact.ColimitRepresentableCone
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LimitConeFamilyReadback

/-!
概要：元の余極限からの全 Hom の極限錐を、標的で添字付けた元の全錐の族へ転置する。
方針：同じ全錐を二変数交換し、頂点・各生成点の評価を元の全共変 Hom へ厳密に戻す。
規約：元の余錐と全 Hom を保持。使われ方：filtered 余極限・有限極限交換への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}

/-- 元の余極限の全 Hom 錐を、同じ標的全体で添字付けた全錐族へ転置する。 -/
def colimitRepresentableFamily (c : JoinCocone D) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K.op))).obj
        SpaceInfinity.{u} :=
  internalHomFlipHomEquiv _ _ _ (colimitRepresentableCone c).val

/-- 元の標的での族の頂点は、同じ全 Hom 錐を同じ標的で評価した関手そのもの。 -/
lemma colimitRepresentableFamily_vertex (c : JoinCocone D) (y : C _⦋0⦌) :
    (colimitRepresentableFamily c).app (Opposite.op ⦋0⦌) (ULift.up y) =
      functorVertex ((colimitRepresentableCone c).val ≫ evaluateFunctorAt (ULift.up y)) :=
  internalHomFlipHomEquiv_app_zero _ _

/-- 元の余錐が余極限なら、同じ全錐族の各点は元の全 Hom の極限錐。 -/
lemma colimitRepresentableFamily_isLimit (c : JoinCocone D) (hc : IsColimitCone c)
    (y : C _⦋0⦌) :
    IsLimitCone (functorVertexCone
      ((colimitRepresentableFamily c).app (Opposite.op ⦋0⦌) (ULift.up y))) := by
  rw [colimitRepresentableFamily_vertex]
  exact (isLimitCone_functorVertexCone_functorVertex
    (evaluateFunctorCone (colimitRepresentableCone c) (ULift.up y))).mpr
    (colimitRepresentableCone_isPointwiseLimit c hc (ULift.up y))

/-- 元の全錐族の頂点評価は、元の余極限頂点からの全 Hom 関手を厳密に回収。 -/
lemma colimitRepresentableFamily_apex (c : JoinCocone D) :
    colimitRepresentableFamily c ≫ evaluateFunctorAt
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj K.op))) =
      covariantRepresentableInfinity c.vertex := by
  apply functorVertex_injective
  rw [colimitRepresentableFamily, flipFamily_evaluate_vertex]
  exact colimitRepresentableCone_vertex c

/-- 元の各生成点での全評価は、その元の項からの全共変 Hom 関手そのもの。 -/
lemma colimitRepresentableFamily_right (c : JoinCocone D) (k : K _⦋0⦌) :
    colimitRepresentableFamily c ≫ evaluateFunctorAt
      ((joinInr (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K.op)).app
        (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm k))) =
      covariantRepresentableInfinity (D.app (Opposite.op ⦋0⦌) k) := by
  apply functorVertex_injective
  rw [colimitRepresentableFamily, flipFamily_evaluate_vertex]
  change ((joinInr _ _ ≫ (colimitRepresentableCone c).val).app (Opposite.op ⦋0⦌))
    (ULift.up (SSet.opObjEquiv.symm k)) = _
  rw [(colimitRepresentableCone c).property]
  change (covariantRepresentableDiagram C).app (Opposite.op ⦋0⦌)
    (ULift.up (SSet.opObjEquiv.symm (D.app (Opposite.op ⦋0⦌) k))) = _
  exact covariantRepresentableDiagram_vertex _

end SerrePositivity.InfinityCategories.F2.Compact
