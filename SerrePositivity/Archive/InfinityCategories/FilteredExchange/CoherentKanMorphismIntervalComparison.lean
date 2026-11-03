module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanRefinementCrossEndpoint

/-!
概要：固定した元の Kan 射で、同じ左右区間の指定比較を保持する。
方針：元の射の退化辺の始点比較の両端だけを厳密に戻す。
規約：新しい path を選ばない。使われ方：三角形の両端比較を同じ射の比較へ統一。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "H" => SimplicialCategory.sHom K L

/-- 元の Kan 射の退化辺の実始点は、元の同じ射の頂点。 -/
lemma coherentKanMorphismDegenerate_source :
    (H).δ 1 ((H).σ 0 (functorVertex f)) = functorVertex f :=
  (SSet.Edge.id (functorVertex f)).src_eq

/-- 元の Kan 射での、同じ二側区間比較の指定成分。 -/
def coherentKanMorphismIntervalComparison :
    VertexIso
      ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm (functorVertex f))))
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (functorVertex f))) :=
  vertexIsoOfEq (coherentKanRefinementSourceComparison K L ((H).σ 0 (functorVertex f)))
    (congrArg (fun t => (coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm t))) (coherentKanMorphismDegenerate_source f))
    (congrArg (fun t => (coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up t)) (coherentKanMorphismDegenerate_source f))

/-- 始点が元の射を表す精密化の比較は、同じ射の指定成分と値まで一致する。 -/
lemma coherentKanRefinementSourceComparison_heq_morphism (e : (H) _⦋1⦌)
    (h : (H).δ 1 e = functorVertex f) :
    HEq (coherentKanRefinementSourceComparison K L e)
      (coherentKanMorphismIntervalComparison f) :=
  (coherentKanRefinementSourceComparison_heq_of_source K L e
    ((H).σ 0 (functorVertex f)) (h.trans (coherentKanMorphismDegenerate_source f).symm)).trans
      (vertexIsoOfEq_heq _ _ _).symm

/-- 終点が元の射を表す精密化でも、同じ射の指定成分と値まで一致する。 -/
lemma coherentKanRefinementTargetComparison_heq_morphism (e : (H) _⦋1⦌)
    (h : (H).δ 0 e = functorVertex f) :
    HEq (coherentKanRefinementTargetComparison K L e)
      (coherentKanMorphismIntervalComparison f) :=
  (coherentKanRefinementTargetComparison_heq_sourceComparison K L e
    ((H).σ 0 (functorVertex f)) (h.trans (coherentKanMorphismDegenerate_source f).symm)).trans
      (vertexIsoOfEq_heq _ _ _).symm

end SerrePositivity.InfinityCategories.F2
