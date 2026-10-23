module
public import SerrePositivity.KST.Fibration.FunctorIsoValue
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoCurryPointComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan

/-! # 同じ指定同型の curry と制限の頂点評価を、再選択せずに比較する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 端点の関手表示と指定同型の HEq は、同じ頂点評価でも保たれる。 -/
theorem functorIsoValue_heq_of_heq {K Y : SSet.{u}} {F G F' G' : K ⟶ Y}
    (e : FunctorIso F G) (e' : FunctorIso F' G')
    (hF : F = F') (hG : G = G') (he : HEq e e') (x : K _⦋0⦌) :
    HEq (functorIsoValue e x) (functorIsoValue e' x) := by
  cases hF
  cases hG
  cases eq_of_heq he
  rfl

/-- 評価点の表示変更でも、元の同じ頂点評価の値を保持する。 -/
theorem functorIsoValue_point_heq {K Y : SSet.{u}} {F G : K ⟶ Y}
    (e : FunctorIso F G) {x x' : K _⦋0⦌} (h : x = x') :
    HEq (functorIsoValue e x) (functorIsoValue e x') := by
  cases h
  rfl

/-- curry の元の頂点は、同じ係数を固定した制限写像の関手頂点。 -/
theorem curry_vertex_functorVertex {A B Y : SSet.{u}}
    (F : A ⊗ B ⟶ Y) (b : B _⦋0⦌) :
    (curry F).app (Opposite.op ⦋0⦌) b =
      functorVertex (lift (𝟙 A) (SSet.const b) ≫ F) := by
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌) (functorVertex F))
    (F2.functorSpaceCurryMap_evaluate (X := Y) b)
  change (evaluateFunctorAt b).app (Opposite.op ⦋0⦌)
    ((functorSpaceCurryMap A B Y).app (Opposite.op ⦋0⦌) (functorVertex F)) = _ at he
  rw [functorSpaceCurryMap_vertex, evaluateFunctorAt_functorVertex] at he
  exact he

/-- 端点だけを揃えた同じ頂点評価は、元の評価写像による像と HEq。 -/
theorem functorIsoValue_heq_map {K Y : SSet.{u}} {F G : K ⟶ Y}
    (e : FunctorIso F G) (x : K _⦋0⦌) :
    HEq (functorIsoValue e x) (VertexIso.map e (evaluateFunctorAt x)) :=
  F2.iso_endpoints_heq _
    (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x F))
    (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x G))

/-- curry の同じ頂点評価は、同じ係数に制限した元の指定同型と HEq。 -/
theorem functorIsoValue_curry_heq_precomp {A B Y : SSet.{u}} [Quasicategory Y]
    {F G : A ⊗ B ⟶ Y} (e : FunctorIso F G) (b : B _⦋0⦌) :
    HEq (functorIsoValue e.curry b) (e.precomp (lift (𝟙 A) (SSet.const b))) := by
  have h := F2.vertexIso_map_heq_of_heq e.curry
    (VertexIso.map e (functorSpaceCurryMap A B Y))
    (functorSpaceCurryMap_vertex F).symm (functorSpaceCurryMap_vertex G).symm
    (F2.functorIso_curry_heq_map e) (evaluateFunctorAt b)
  refine (functorIsoValue_heq_map e.curry b).trans (h.trans ?_)
  rw [F2.vertexIso_map_comp, F2.functorIso_precomp_eq_mapIso]
  exact F2.vertexIso_map_heq e (F2.functorSpaceCurryMap_evaluate b)

/-- 同じ制限同型を評価すると、元の指定同型を像の点で評価した値と一致する。 -/
theorem functorIsoValue_precomp {A B Y : SSet.{u}} {F G : B ⟶ Y}
    (e : FunctorIso F G) (q : A ⟶ B) (a : A _⦋0⦌) :
    functorIsoValue (e.precomp q) a = functorIsoValue e (q.app (Opposite.op ⦋0⦌) a) := by
  have h := functorIsoValue_heq_map (e.precomp q) a
  rw [F2.functorIso_precomp_eq_mapIso] at h
  have hc := F2.vertexIso_map_comp e ((pre q).app Y) (evaluateFunctorAt a)
  have hp := F2.vertexIso_map_heq e (evaluateFunctorAt_pre q a)
  exact eq_of_heq (h.trans ((heq_of_eq hc).trans
    (hp.trans (functorIsoValue_heq_map e (q.app (Opposite.op ⦋0⦌) a)).symm)))

end SerrePositivity.KST.Fibration
