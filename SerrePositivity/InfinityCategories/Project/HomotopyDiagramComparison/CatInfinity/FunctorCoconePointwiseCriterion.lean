module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalenceAllLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CosliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.OppositeFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity

/-- 概要：全評価が余極限余錐となる関手圏内の余錐は余極限余錐。
方針：反転した錐に関手圏の点ごとの極限判定を適用する。
規約：添字と関手の始域は任意の単体集合。
使われ方：矢印圏の両端による余極限判定。 -/
lemma isColimitCone_functor_of_pointwise {J K C : SSet.{u}} [Quasicategory C]
    {r : J ⟶ (ihom K).obj C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (hc : ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone c).2
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isLimitCone_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c)).2
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_pointwise
  intro k'
  obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k'
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ ?_).2
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_reverse_postcomp_iff c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).2 (hc k))
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c).val ≫ e.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c).val ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)
  rw [Category.assoc]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso K C).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.opObjEquiv.symm k) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.oppositeInternalHom_evaluate]

/-- 概要：両端で余極限余錐となる矢印圏内の余錐は余極限余錐。
方針：区間の二頂点を列挙し、点ごとの余極限判定を使う。
規約：元の指定余錐は変更しない。
使われ方：Tamme Lemma 8(i) の矢印成分。 -/
lemma isColimitCone_arrow_of_endpoints {J C : SSet.{u}} [Quasicategory C]
    {r : J ⟶ (ihom (Δ[1] : SSet.{u})).obj C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) c))
    (h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply isColimitCone_functor_of_pointwise
  intro k
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  fin_cases i
  · exact h0
  · exact h1

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity
