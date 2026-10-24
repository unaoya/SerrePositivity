module

public import SerrePositivity.InfinityCategories.F2.Presentable.LimitMappingComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.MappingOpposite
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.CoconeVertex

/-!
概要：指定余極限で表された始域からの元の写像空間比較を、その各項の比較から回収。
方針：同じ全余錐を反転し、全共変 Hom の極限保存と元の反転比較の同値性を使う。
規約：元の関手・余錐・両対象・pinchedHomMap を保持する。
使われ方：Ind 比較の全充満忠実性の始域変数での生成拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 同じ元の余極限を保存する関手の写像空間比較は、始域の各項から頂点へ延長する。 -/
lemma pinchedHomMap_equivalence_of_source_colimit {K C E : SSet.{u}}
    [Quasicategory C] [Quasicategory E] (G : C ⟶ E) (y : C _⦋0⦌)
    {D : K ⟶ C} (c : JoinCocone D) (hc : IsColimitCone c)
    (hGc : IsColimitCone (mapJoinCocone G c))
    (ht : ∀ j : K _⦋0⦌, IsSimplicialHomotopyEquivalence
      (pinchedHomMap G (D.app (Opposite.op ⦋0⦌) j) y)) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap G c.vertex y) := by
  apply (pinchedHomMap_equivalence_iff_op G c.vertex y).mpr
  have h := pinchedHomMap_equivalence_of_limit (SSet.opFunctor.map G)
    (SSet.opObjEquiv.symm y) (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c)
    ((SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone c).mp hc)
    ((isLimitCone_reverse_postcomp_iff c G).mpr hGc) (by
      intro j
      exact (pinchedHomMap_equivalence_iff_op G
        (D.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv j)) y).mp (ht (SSet.opObjEquiv j)))
  rwa [SerrePositivity.InfinityCategories.F1B.coconeReverseCone_vertex] at h

end SerrePositivity.InfinityCategories.F2.Presentable
