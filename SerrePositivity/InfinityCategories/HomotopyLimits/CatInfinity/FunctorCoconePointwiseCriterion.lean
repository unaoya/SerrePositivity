module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.F1B.Cones.CosliceOpposite
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeValEquality
public import SerrePositivity.InfinityCategories.HomotopyLimits.CatInfinity.OppositeFunctorEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeInternalHom

/-!
概要：関手圏の指定余錐の点ごとの余極限性からの判定。
方針：指定評価を保つ反転同型で点ごとの極限判定へ移す。
規約：元の余錐と評価点を全射の等式で照合する。
使われ方：lax pullback の矢印成分の余極限性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：全評価が余極限余錐となる関手圏内の余錐は余極限余錐。
方針：反転した錐に関手圏の点ごとの極限判定を適用する。
規約：添字と関手の始域は任意の単体集合。
使われ方：矢印圏の両端による余極限判定。 -/
lemma isColimitCone_functor_of_pointwise {J K C : SSet.{u}} [Quasicategory C]
    {r : J ⟶ (ihom K).obj C} (c : JoinCocone r)
    (hc : ∀ k : K _⦋0⦌,
      IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt k) c)) :
    IsColimitCone c := by
  let e := HomotopyLimits.oppositeInternalHomIso K C
  apply (SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone c).2
  apply ((qCatEquivalenceOfIso e).isLimitCone_iff (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c)).2
  apply isLimitCone_of_pointwise
  intro k'
  obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k'
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2
    ((isLimitCone_reverse_postcomp_iff c (evaluateFunctorAt k)).2 (hc k))
  change ((SerrePositivity.InfinityCategories.F1B.coconeReverseCone c).val ≫ e.hom) ≫
    evaluateFunctorAt (SSet.opObjEquiv.symm k) =
      (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c).val ≫ SSet.opFunctor.map (evaluateFunctorAt k)
  rw [Category.assoc]
  change _ ≫ (HomotopyLimits.oppositeInternalHomIso K C).hom ≫
    evaluateFunctorAt (SSet.opObjEquiv.symm k) = _
  rw [oppositeInternalHom_evaluate]

/-- 概要：両端で余極限余錐となる矢印圏内の余錐は余極限余錐。
方針：区間の二頂点を列挙し、点ごとの余極限判定を使う。
規約：元の指定余錐は変更しない。
使われ方：Tamme Lemma 8(i) の矢印成分。 -/
lemma isColimitCone_arrow_of_endpoints {J C : SSet.{u}} [Quasicategory C]
    {r : J ⟶ (ihom (Δ[1] : SSet.{u})).obj C} (c : JoinCocone r)
    (h0 : IsColimitCone (F1B.kanPostcomposeCocone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) c))
    (h1 : IsColimitCone (F1B.kanPostcomposeCocone
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) c)) : IsColimitCone c := by
  apply isColimitCone_functor_of_pointwise
  intro k
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases i
  · exact h0
  · exact h1

end SerrePositivity.InfinityCategories.F2
