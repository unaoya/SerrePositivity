module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaCoconeFamily
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.FunctorCoconePointwiseCriterion

/-!
概要：全余錐族の点ごとの補完の下方図式を、元の指定単一表示の図式へ同定する。
方針：同じ下方全余錐の普遍性と元の標準全余錐の一意性を使う。
規約：全図式間の関手同型であり、各点だけの同値へ弱めない。
使われ方：I-2 c の完成後の実四角形を元の指定四角形へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ全余錐族の点ごとの補完の下方は、元の指定全図式と関手同型である。 -/
def indCoconeCompletionBaseIso (κ : Cardinal.{u}) {I K C : SSet.{u}} [Quasicategory C]
    (a : I ⟶ (ihom K).obj C)
    (l : I ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (hl : l ≫ coconeRestriction K C = a)
    (c : JoinCocone (indYonedaCoconeFamily κ l)) (hp : IsPointwiseColimitCone c)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
    (d : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C))
    (hd : IsColimitCone d) (hdv : d.vertex = functorVertex D) :
    FunctorIso (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj K) (Δ[0] : SSet.{u + 1}) ≫
      (functorVertexCocone c.vertex).val) D := by
  let j := joinInl ((SSet.uliftFunctor.{u + 1, u}).obj K) (Δ[0] : SSet.{u + 1})
  let q := reindexFunctorCocone c j
  have hq : IsColimitCone q := isColimitCone_functor_of_pointwise q (hp.reindex j)
  have he : indYonedaCoconeFamily κ l ≫ (pre j).app (IndInfinity κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C := by
    change indYonedaCoconeFamily κ l ≫ coconeRestriction _ _ = _
    rw [indYonedaCoconeFamily_restriction, hl]
  let q' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ diagramYoneda κ K C) :=
    ⟨q.val, q.property.trans he⟩
  have hq' : IsColimitCone q' :=
    (isColimitCone_iff_of_coconeMap_eq q' q rfl).mpr hq
  have e := colimitVertexIso q' d hq' hd
  have hv : functorVertex (j ≫ (functorVertexCocone c.vertex).val) = q'.vertex := by
    change functorVertex (j ≫ (functorVertexEquiv _ _).symm c.vertex) =
      ((pre j).app (IndInfinity κ C)).app (Opposite.op ⦋0⦌) c.vertex
    apply (functorVertexEquiv _ _).symm.injective
    change (functorVertexEquiv _ _).symm
      ((functorVertexEquiv _ _) (j ≫ (functorVertexEquiv _ _).symm c.vertex)) = _
    rw [Equiv.symm_apply_apply, functorVertexMap_precomp]
  change VertexIso (functorVertex (j ≫ (functorVertexCocone c.vertex).val)) (functorVertex D)
  rw [hv, ← hdv]
  exact e

end SerrePositivity.InfinityCategories.F2.Ind
