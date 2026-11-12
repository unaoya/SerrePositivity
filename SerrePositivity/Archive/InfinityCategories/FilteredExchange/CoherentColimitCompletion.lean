module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFamilyColimitCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyFunctor

/-!
概要：元の点ごとの指定余錐による完成を、余極限関手による元の全錐の像へ比較する。
方針：二変数交換で標準余錐を戻し、元の全錐の頂点同型と極限性の不変性を使う。
規約：任意の指定余錐を扱う。使われ方：有限極限交換を余極限関手の保存性へ帰着する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) {A : SSet.{u + 1}}
  (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ (ihom A).obj SpaceInfinity.{u})

/-- 元の図式を厳密に保ち、余極限関手から作った標準の点ごとの余錐。 -/
def coherentPointwiseColimitCocone : JoinCocone p :=
  ⟨(coherentFamilyColimitCocone B (internalHomFlipHomEquiv _ _ _ p)).val, by
    apply (coherentFamilyColimitCocone B (internalHomFlipHomEquiv _ _ _ p)).property.trans
    exact (internalHomFlipHomEquiv _ _ _).left_inv p⟩

/-- 元の図式を保つ標準余錐は全てのパラメータで余極限。 -/
lemma coherentPointwiseColimitCocone_pointwise :
    IsPointwiseColimitCone (coherentPointwiseColimitCocone B p) := by
  intro a
  apply (isColimitCone_iff_of_coconeMap_eq
    (evaluateFunctorCocone (coherentPointwiseColimitCocone B p) a) (evaluateFunctorCocone
    (coherentFamilyColimitCocone B (internalHomFlipHomEquiv _ _ _ p)) a) rfl).mpr
  exact coherentFamilyColimitCocone_pointwise B (internalHomFlipHomEquiv _ _ _ p) a

/-- 標準の元の完成頂点は、元の二変数交換に余極限関手を適用した関手頂点。 -/
lemma coherentPointwiseColimitCocone_vertex :
    (coherentPointwiseColimitCocone B p).vertex = functorVertex
      (internalHomFlipHomEquiv _ _ _ p ≫ coherentColimitFunctor B) :=
  coherentFamilyColimitCocone_vertex B (internalHomFlipHomEquiv _ _ _ p)

/-- 元の任意の指定余極限余錐の頂点と、余極限関手による元の族の像との同型。 -/
def coherentPointwiseColimitVertexIso (c : JoinCocone p) (hc : IsPointwiseColimitCone c) :
    VertexIso c.vertex (functorVertex
      (internalHomFlipHomEquiv _ _ _ p ≫ coherentColimitFunctor B)) := by
  have e := pointwiseColimitConeVertexIso c (coherentPointwiseColimitCocone B p) hc
    (coherentPointwiseColimitCocone_pointwise B p)
  rw [coherentPointwiseColimitCocone_vertex] at e
  exact e

/-- 元の指定余錐で完成した全錐の極限性は、元の関手錐の余極限関手による像で判定可能。 -/
lemma coherentCompletedLimit_iff_colimitFunctor {K : SSet.{u + 1}}
    (q : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) K)).obj SpaceInfinity.{u})
    (c : JoinCocone q) (hc : IsPointwiseColimitCone c) :
    IsLimitCone (functorVertexCone c.vertex) ↔
      IsLimitCone (mapJoinCone (coherentColimitFunctor B) (pointwiseLimitFamilyCone q)) := by
  have e := coherentPointwiseColimitVertexIso B q c hc
  exact (isLimitCone_functorVertexCone_iff_of_vertexIso e).trans
    (isLimitCone_functorVertexCone_functorVertex
      (mapJoinCone (coherentColimitFunctor B) (pointwiseLimitFamilyCone q)))

end SerrePositivity.InfinityCategories.F2
