module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparisonColimitClass
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Core.Compact.UniverseCoconePostcomposition

/-!
概要：元の全共変 Hom 比較の可逆成分を、compact 性で小さい filtered 余極限へ拡張。
方針：両側の同じ全 Hom による保存と、指定余錐の宇宙・後合成の一致を使う。
規約：κ と添字は u、圏は u+1。元の全比較と元の余錐を固定する。
使われ方：Ind 比較の生成対象から任意の Ind 対象への拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- compact な始点とその像の同じ全 Hom 比較は、元の filtered 余極限頂点へ延長する。 -/
lemma covariantHomComparison_component_colimit {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : IsKappaAccessibleFunctor κ G) (x : C _⦋0⦌)
    (hx : Compact.IsKappaCompact.{u, u + 1} κ x)
    (hGx : Compact.IsKappaCompact.{u, u + 1} κ (G.app (Opposite.op ⦋0⦌) x))
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C) (c : JoinCocone D) (hc : IsColimitCone c)
    (ht : ∀ j : I _⦋0⦌, IsIso ((hoFunctor.map (evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj C) (Y := SpaceInfinity.{u + 1})
      (ULift.up (D.app (Opposite.op ⦋0⦌) (ULift.up j))))).toFunctor.map
        (covariantHomComparison G x))) :
    IsIso ((hoFunctor.map (evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj C) (Y := SpaceInfinity.{u + 1})
      (ULift.up c.vertex))).toFunctor.map (covariantHomComparison G x)) := by
  have hF := hx I D c hc
  have hT : IsColimitCone (mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫
        covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) (JoinCocone.ulift c)) := by
    rw [Compact.mapJoinCocone_universe_comp]
    exact hGx I (D ≫ G) (mapJoinCocone G c) (hG I D c hc)
  have h := functorHomComparison_colimit_vertex (JoinCocone.ulift c)
    (covariantHomComparison G x) hF hT (by
      rintro ⟨⟨j⟩⟩
      exact ht j)
  have hv : (JoinCocone.ulift.{u + 1, u + 2} c).vertex = ULift.up c.vertex :=
    JoinCocone.ulift_vertex c
  rw [hv] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
