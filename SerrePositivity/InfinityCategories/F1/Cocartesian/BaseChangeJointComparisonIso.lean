module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeJointComparisonEvaluation
public import SerrePositivity.InfinityCategories.F1.Coherent.QCatInvertible

/-!
概要：元の分類主写像の底変換比較を、底全体・全 fibration の関手同型にする。
方針：同じ辺を二変数で評価し、元の底変換比較成分の同値性を使う。
規約：別の成分や別の分類写像を選び直さない。
使われ方：同じ分類主写像の Hom 作用のセル制限による降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 頂点表示を固定しない関手空間の辺にも、同じ点ごとの可逆性判定を使える。 -/
lemma isInvertibleEdge_iff_evaluateFunctorAt_vertices
    {K X : SSet.{u}} [Quasicategory X] {a b : ((ihom K).obj X) _⦋0⦌}
    (e : SSet.Edge a b) :
    IsInvertibleEdge e.toTruncated ↔ ∀ k : K _⦋0⦌,
      IsInvertibleEdge (e.map (evaluateFunctorAt k)).toTruncated := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv K X).surjective a
  obtain ⟨g, rfl⟩ := (functorVertexEquiv K X).surjective b
  exact isInvertibleEdge_iff_evaluateFunctorAt e.toTruncated

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)

/-- 底全体と全 fibration の同じ比較の辺は、各成分の同値性により可逆。 -/
lemma cocartesianBaseChangeJointComparisonEdge_isInvertible :
    IsInvertibleEdge (cocartesianBaseChangeJointComparisonEdge k).toTruncated := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt
    (cocartesianBaseChangeJointComparisonEdge k).toTruncated).mpr
  intro s
  rw [← coherentNerveVertex_object s]
  change IsInvertibleEdge (functorEdgeAt (cocartesianBaseChangeJointComparisonEdge k)
    (coherentNerveVertex (coherentNerveObject s))).toTruncated
  apply (isInvertibleEdge_iff_evaluateFunctorAt_vertices
    (functorEdgeAt (cocartesianBaseChangeJointComparisonEdge k)
      (coherentNerveVertex (coherentNerveObject s)))).mpr
  rintro ⟨v⟩
  obtain ⟨d, rfl⟩ : ∃ d : D, v = nerveVertex d :=
    ⟨v.obj 0, ComposableArrows.ext₀ rfl⟩
  apply (isInvertibleEdge_congr
    (cocartesianBaseChangeJointComparisonEdge_at k (coherentNerveObject s) d)).mpr
  exact coherentQCatEdge_isInvertible_of_isQCatEquivalence
    (cocartesianStrictTransportBaseChangeComponent_isQCatEquivalence
      (coherentNerveObject s).val.hom k d)

/-- 同じ分類主写像の制限と底変換後の分類主写像の、全体にわたる関手同型。 -/
def cocartesianBaseChangeJointComparisonIso :
    FunctorIso (cocartesianStraighteningCoherentMap C ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app CatInfinity.{u})
      (cocartesianFibrationInfinityBaseChange (nerveMap k) ≫
        cocartesianStraighteningCoherentMap D) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (cocartesianBaseChangeJointComparisonEdge k).toTruncated) :=
    cocartesianBaseChangeJointComparisonEdge_isInvertible k
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (cocartesianBaseChangeJointComparisonEdge k).toTruncated)

end SerrePositivity.InfinityCategories
