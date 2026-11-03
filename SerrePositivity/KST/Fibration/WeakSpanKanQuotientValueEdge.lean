module
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningSimplexRestriction
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientPointedComparison
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientFiberUnit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpaceHomotopyClasses
public import SerrePositivity.InfinityCategories.Stable.FunctorHoEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoTriangleEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoVertexEvaluation
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.FunctorIsoComponentPre
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorIsoDisplayComponent

/-!
概要：同じ実商比較の transport 辺を元の降下同型の指定成分へ照合する。
方針：元の全関手空間の代表辺を元の単体頂点で評価する。
規約：元の降下同型・単体・値の射を保持する。一般の transport API は追加しない。
使われ方：K-B-S の全 fiber 単位と既存指定恒等点の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌) (c : TransportSimplexCategory B.obj)

/-- 概要：同じ実商比較の fiber 作用を与える、元の指定成分の実辺。
方針：同じ全変換のパラメータを元の単体の頂点で評価する。
規約：比較辺を選び直さない。
使われ方：元の商値比較辺との合成の正規化。 -/
def weakSpanKanQuotientForwardValueEdge :=
  functorEdgeAt (intervalMappingEdgeOfVertex
    (smallUnstraighteningHomParameter (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom))
    (ULift.up (nerveVertex c))

/-- 概要：同じ実比較辺は元の全降下同型の逆の指定成分を表す。
方針：元の全関手空間の代表辺の類を頂点評価で読む。
規約：全一単体の構成と同じ成分を使う。
使われ方：指定値比較による全 fiber の正規化。 -/
theorem weakSpanKanQuotientForwardValueEdge_hom :
    Truncated.HomotopyCategory.homMk (weakSpanKanQuotientForwardValueEdge h x c).toTruncated =
      (FunctorIso.app (weakSpanKanQuotientDiagram_simplexIso h x).symm
        (ULift.up (nerveVertex c))).hom := by
  let e := (weakSpanKanQuotientDiagram_simplexIso h x).symm
  let v : ((SSet.uliftFunctor.{u + 1, u}).obj
      (nerve (TransportSimplexCategory B.obj))) _⦋0⦌ := ULift.up (nerveVertex c)
  let ev := (hoFunctor.map (evaluateFunctorAt (Y := SpaceInfinity.{u}) v)).toFunctor
  have he := smallUnstraighteningHomEdge_hom e.hom
  apply Arrow.mk_injective _ _
  calc
    _ = Arrow.mk (ev.map (Truncated.HomotopyCategory.homMk
        (smallUnstraighteningHomEdge e.hom).toTruncated)) := by
      apply Truncated.HomotopyCategory.congr_arrowMk_homMk
      change (functorEdgeAt (intervalMappingEdgeOfVertex
        (intervalMappingVertexOfEdge (smallUnstraighteningHomEdge e.hom))) v).edge =
        ((smallUnstraighteningHomEdge e.hom).map (evaluateFunctorAt v)).edge
      have h := (intervalMappingEdgeVertexEquiv _ _).left_inv (smallUnstraighteningHomEdge e.hom)
      change intervalMappingEdgeOfVertex
        (intervalMappingVertexOfEdge (smallUnstraighteningHomEdge e.hom)) = _ at h
      rw [h]
      rfl
    _ = Arrow.mk (ev.map e.hom) := congrArg (fun a => Arrow.mk (ev.map a)) he
    _ = _ := (functorIso_toNatIso_hom_app_arrow e v).symm



/-- 概要：同じ全降下同型の成分を元の Kan 値へ戻すと既存指定値同型そのもの。
方針：元の全関手同型の合成と前合成の頂点評価を使う。
規約：元の値座標への厳密な等式輸送だけを追加する。
使われ方：同じ実比較辺と既存の商値正規化との接続。 -/
theorem weakSpanKanQuotientSimplexIso_app_value :
    FunctorIso.app (weakSpanKanQuotientDiagram_simplexIso h x)
        (ULift.up (nerveVertex c)) ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (kanDiagramCoherentNerve_vertex (weakSpanKanDiagram i x) c)) =
      weakSpanKanQuotientDiagram_initialVertexIso h x c := by
  have hp := F2.functorIso_app_precomp_heq (weakSpanKanQuotientDiagram_restrictionIso h x)
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (ULift.up (nerveVertex c))
  have hp' := eq_of_heq hp
  simp only [weakSpanKanQuotientDiagram_simplexIso, FunctorIso.app_trans,
    weakSpanKanQuotientDiagram_initialVertexIso, weakSpanKanSpaceDiagram_initialVertexIso,
    Iso.trans_assoc]
  have hd := F2.functorIsoOfEq_app_heq
    ((weakSpanKanQuotientDiagram_restrictionIso h x).precomp
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj)))
    (by rw [← Category.assoc, ← Functor.map_comp]) rfl (ULift.up (nerveVertex c))
  have hd' := eq_of_heq hd
  rw [hd', hp']
  rfl


/-- 概要：同じ実比較辺の始点だけを、元の同じ Kan 図式値に厳密に揃える。
方針：元の coherent 図式の頂点公式による等式輸送を使う。
規約：元の全一単体を変更しない。
使われ方：既存指定値比較の逆辺との合成。 -/
def weakSpanKanQuotientForwardValueEdgeAtValue :
    SpaceInfinity.{u}.Edge (spaceInfinityVertex ((weakSpanKanDiagram i x).obj c))
      ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
          ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))))) :=
  (weakSpanKanQuotientForwardValueEdge h x c).ofEq
    (kanDiagramCoherentNerve_vertex (weakSpanKanDiagram i x) c) rfl

/-- 概要：元の Kan 値へ座標を揃えた同じ実辺は既存指定値同型の逆を表す。
方針：同じ実辺の類と元の全降下成分の照合を使う。
規約：既存指定値同型を別のものに置き換えない。
使われ方：全 fiber 単位の元の値比較による正規化。 -/
theorem weakSpanKanQuotientForwardValueEdgeAtValue_hom :
    Truncated.HomotopyCategory.homMk
      (weakSpanKanQuotientForwardValueEdgeAtValue h x c).toTruncated =
        (weakSpanKanQuotientDiagram_initialVertexIso h x c).inv := by
  rw [weakSpanKanQuotientForwardValueEdgeAtValue, homMk_edge_ofEq,
    weakSpanKanQuotientForwardValueEdge_hom, FunctorIso.app_symm]
  simp only [eqToHom_refl, Category.comp_id, Iso.symm_hom]
  exact congrArg Iso.inv (weakSpanKanQuotientSimplexIso_app_value h x c)

end SerrePositivity.KST.Fibration
