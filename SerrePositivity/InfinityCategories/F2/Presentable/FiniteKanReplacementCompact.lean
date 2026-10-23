module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteSimplicialHomAccessible
public import SerrePositivity.InfinityCategories.F2.Presentable.SimplicialHomSourceComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallSpaceCompact

/-!
概要：有限単体集合の元の連続 Kan 置換が、N の定義で compact になる。
方針：有限始点の全 filtered 保存を Kan 置換からの全 Hom へ自然同型で移し、元の大きい共変 Hom と比較する。
規約：元の指定全余錐の像を保持。Kan 置換の台の有限性は仮定しない。
使われ方：空間の小さい compact 生成圏の有限模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の小さい全 Hom の保存性から、同じ Kan 対象の大きい全共変 Hom による compact 性を得る。 -/
lemma kanObject_isKappaCompact_of_homPreservation {κ : Cardinal.{u}} (K : KanObject.{u})
    (h : IsKappaAccessibleFunctor κ (kanInternalHomInfinity K)) :
    Compact.IsKappaCompact.{u, u + 1} κ (coherentNerveVertex K) := by
  intro I hI hFiltered D c hc
  have hm : IsColimitCone (mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (kanInternalHomInfinity K) ≫
        Compact.spaceUniverseDiagram) (JoinCocone.ulift c)) := by
    rw [Compact.mapJoinCocone_universe_comp]
    exact Compact.spaceUniverseDiagram_map_isColimit (D ≫ kanInternalHomInfinity K)
      (mapJoinCocone (kanInternalHomInfinity K) c) (h I D c hc)
  exact hm.of_functorIso ((kanHom_covariantModelIso K).precomp (JoinCocone.ulift c).val).symm

/-- 有限単体集合の元の Kan 置換は、一般の小さい filtered ∞ 余極限に対して compact。 -/
lemma finiteKanReplacement_isCompact (A : SSet.{u}) [A.Finite] :
    Compact.IsKappaCompact.{u, u + 1} Cardinal.aleph0
      (coherentNerveVertex (continuousReplacementKanObject A)) :=
  kanObject_isKappaCompact_of_homPreservation _
    ((finiteSimplicialHomInfinity_isKappaAccessibleFunctor A).of_functorIso
      (continuousReplacementHomIso A).symm)

end SerrePositivity.InfinityCategories.F2.Presentable
