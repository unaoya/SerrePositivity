module

public import SerrePositivity.InfinityCategories.F2.Ind.DensityHomotopyDetection
public import SerrePositivity.InfinityCategories.F2.Ind.ContinuousFunctorRestriction
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-!
概要：元の Yoneda による実際の制限射は、κ-filtered 保存関手間の同値を反映する。
方針：元の関手辺を同じ密度余錐上のホモトピーに戻し、全頂点の可逆性から元の辺を判定する。
規約：制限射の充満忠実性や本質的全射性は仮定しない。
使われ方：HTT 5.3.5.10 の実際の制限写像の比較における同値の検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 保存関手間の指定辺は、元の Yoneda による制限が可逆なら可逆。 -/
lemma continuousFunctorEdge_isInvertible_of_restriction {F G : IndInfinity κ C ⟶ D}
    (hF : PreservesSmallKappaFilteredColimits κ F)
    (hG : PreservesSmallKappaFilteredColimits κ G)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (IndInfinity κ C)).obj D))
      (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge
      (X := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D) (e.map ((truncation 2).map ((pre (indYoneda κ C)).app D)))) :
    IsInvertibleEdge e := by
  have hH : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge
      (simplicialHomotopyOfFunctorEdge e)
      ((indYoneda κ C).app (Opposite.op ⦋0⦌) x)).toTruncated := by
    intro x
    have hm := he.map (evaluateFunctorAt (Y := D) x)
    have hx := ConcreteCategory.congr_hom (NatTrans.congr_app
      (evaluateFunctorAt_pre (X := D) (indYoneda κ C) x) (Opposite.op ⦋1⦌)) e.edge
    have hm' : IsInvertibleEdge (X := D)
        (e.map ((truncation 2).map (evaluateFunctorAt
          ((indYoneda κ C).app (Opposite.op ⦋0⦌) x)))) :=
      (isInvertibleEdge_congr (e := (e.map ((truncation 2).map ((pre (indYoneda κ C)).app D))).map
        ((truncation 2).map (evaluateFunctorAt (Y := D) x)))
        (f := e.map ((truncation 2).map (evaluateFunctorAt (Y := D)
          ((indYoneda κ C).app (Opposite.op ⦋0⦌) x)))) hx).mp hm
    exact (isInvertibleEdge_congr (evaluateFunctorAt_edge e _)).mpr hm'
  apply (isInvertibleEdge_iff_evaluateFunctorAt e).mpr
  intro v
  exact (isInvertibleEdge_congr (evaluateFunctorAt_edge e v)).mp
    (continuousHomotopy_vertex_isInvertible hF hG (simplicialHomotopyOfFunctorEdge e) hH v)

/-- 元の保存関手の全部分圏の、実際の制限射そのものは指定辺の可逆性を反映する。 -/
lemma indKappaContinuousRestriction_reflects_isInvertibleEdge
    {x y : (KappaContinuousFunctorInfinity κ (IndInfinity κ C) D) _⦋0⦌}
    (e : SSet.Truncated.Edge
      (X := (truncation 2).obj (KappaContinuousFunctorInfinity κ (IndInfinity κ C) D)) x y)
    (he : IsInvertibleEdge
      (X := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D) (e.map ((truncation 2).map (indKappaContinuousRestriction κ C D)))) :
    IsInvertibleEdge e := by
  let F := (functorVertexEquiv (IndInfinity κ C) D).symm x.val
  let G := (functorVertexEquiv (IndInfinity κ C) D).symm y.val
  have hFv : functorVertex F = x.val := (functorVertexEquiv _ _).apply_symm_apply x.val
  have hGv : functorVertex G = y.val := (functorVertexEquiv _ _).apply_symm_apply y.val
  let m := e.map ((truncation 2).map (kappaContinuousFunctorInclusion κ (IndInfinity κ C) D))
  let e' : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (IndInfinity κ C)).obj D))
      (functorVertex F) (functorVertex G) := {
    edge := m.edge
    src_eq := m.src_eq.trans hFv.symm
    tgt_eq := m.tgt_eq.trans hGv.symm }
  have hF : PreservesSmallKappaFilteredColimits κ F := fullSubcomplexOnVertices_vertex x
  have hG : PreservesSmallKappaFilteredColimits κ G := fullSubcomplexOnVertices_vertex y
  have hi : IsInvertibleEdge
      (X := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D) (e'.map ((truncation 2).map ((pre (indYoneda κ C)).app D))) :=
    (isInvertibleEdge_congr
      (X := (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D)
      (e := e'.map ((truncation 2).map ((pre (indYoneda κ C)).app D)))
      (f := e.map ((truncation 2).map (indKappaContinuousRestriction κ C D))) rfl).mpr he
  have hi' := continuousFunctorEdge_isInvertible_of_restriction hF hG e' hi
  apply IsFullyFaithful.reflects_isInvertibleEdge
    (kappaContinuousFunctorInclusion_isFullyFaithful κ (IndInfinity κ C) D) e
  exact (isInvertibleEdge_congr (X := (ihom (IndInfinity κ C)).obj D) (e := e') (f := m) rfl).mp hi'

end SerrePositivity.InfinityCategories.F2.Ind
