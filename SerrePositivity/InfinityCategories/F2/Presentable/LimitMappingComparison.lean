module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparisonLimit
public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparisonComponent
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableLimitCharacterization

/-!
概要：元の関手が保存する指定極限について、写像空間比較の同値性を頂点へ延長。
方針：全共変 Hom の極限保存と、同じ自然な比較の可逆成分の極限閉性を合成する。
規約：指定された全錐と元の pinchedHomMap を保持。全充満忠実性は仮定しない。
使われ方：反転した Ind の filtered 表示による始域変数の生成拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 同じ指定錐の宇宙持ち上げと二段の後合成は、全錐そのものとして一致。 -/
lemma mapJoinCone_universe_comp {K C E : SSet.{u}} {X : SSet.{u + 1}}
    {D : K ⟶ C} (G : C ⟶ E) (H : (SSet.uliftFunctor.{u + 1, u}).obj E ⟶ X)
    (c : JoinCone D) :
    mapJoinCone ((SSet.uliftFunctor.{u + 1, u}).map G ≫ H) (JoinCone.ulift c) =
      mapJoinCone H (JoinCone.ulift (mapJoinCone G c)) := by
  apply Subtype.ext
  change ((_ ≫ (SSet.uliftFunctor.{u + 1, u}).map c.val) ≫ _) =
    ((_ ≫ (SSet.uliftFunctor.{u + 1, u}).map (c.val ≫ G)) ≫ H)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- 指定極限の各項での元の写像空間比較が同値なら、同じ極限頂点でも同値。 -/
lemma pinchedHomMap_equivalence_of_limit {K C E : SSet.{u}}
    [Quasicategory C] [Quasicategory E] (G : C ⟶ E) (x : C _⦋0⦌)
    {D : K ⟶ C} (c : JoinCone D) (hc : IsLimitCone c)
    (hGc : IsLimitCone (mapJoinCone G c))
    (ht : ∀ j : K _⦋0⦌, IsSimplicialHomotopyEquivalence
      (pinchedHomMap G x (D.app (Opposite.op ⦋0⦌) j))) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap G x c.vertex) := by
  have hF := covariantRepresentableInfinity_isLimit c hc x
  have hT : IsLimitCone (mapJoinCone
      ((SSet.uliftFunctor.{u + 1, u}).map G ≫
        covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) (JoinCone.ulift c)) := by
    rw [mapJoinCone_universe_comp]
    exact covariantRepresentableInfinity_isLimit (mapJoinCone G c) hGc _
  have h := functorHomComparison_limit_vertex (JoinCone.ulift c)
    (covariantHomComparison G x) hF hT (by
      rintro ⟨j⟩
      exact (covariantHomComparison_component_isIso_iff G x _).mpr (ht j))
  have hv : (JoinCone.ulift.{u, u + 1} c).vertex = ULift.up c.vertex := JoinCone.ulift_vertex c
  rw [hv] at h
  exact (covariantHomComparison_component_isIso_iff G x c.vertex).mp h

end SerrePositivity.InfinityCategories.F2.Presentable
