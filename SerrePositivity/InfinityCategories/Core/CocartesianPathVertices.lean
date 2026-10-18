module

public import SerrePositivity.InfinityCategories.Core.CocartesianPathSpace

/-!
概要：cocartesian な辺の path と始点を指定した持ち上げ。
方針：一次単体を関手の頂点へ戻し、二つの射影で基底との一致を確認する。
規約：quasicategory 性は不要。
使われ方：Kerodon §5.1.4 の輸送の存在の零次元の部分。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cocartesian な辺を cocartesian な path の頂点へ写す。
方針：Yoneda 表示を関手の頂点とし、全部分複体へ含める。
規約：p のファイブレーション性は不要。
使われ方：Kerodon §5.1.4 の辺の持ち上げの path 表示。 -/
def cocartesianPathVertex {E B : SSet.{u}} (p : E ⟶ B) {x y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (he : HasCocartesianHornLifting p e) : (cocartesianPathSpace p) _⦋0⦌ :=
  ⟨functorVertex (SSet.yonedaEquiv.symm e.edge), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    rw [op_id, CategoryTheory.Functor.map_id_apply]
    unfold IsCocartesianPathVertex
    apply (hasCocartesianHornLifting_congr p (show
      (intervalFunctorVertexTypedEdge (functorVertex (SSet.yonedaEquiv.symm e.edge))).edge =
        e.edge from by
      change intervalFunctorVertexEdge _ = _
      rw [intervalFunctorVertexEdge_functorVertex, Equiv.apply_symm_apply])).2
    exact he⟩

/-- 概要：cocartesian な path の頂点の始点は元の辺の始点。
方針：評価の Yoneda 表示と辺の始点条件を使う。
規約：p のファイブレーション性は不要。
使われ方：Kerodon §5.1.4 の始点を指定した輸送。 -/
lemma cocartesianPathVertex_zero {E B : SSet.{u}} (p : E ⟶ B) {x y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (he : HasCocartesianHornLifting p e) :
    (cocartesianPathSpaceι p ≫ evaluateFunctorAt (Y := E) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (cocartesianPathVertex p e he) = x := by
  change (evaluateFunctorAt (Y := E) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
    (Opposite.op ⦋0⦌) (functorVertex (SSet.yonedaEquiv.symm e.edge)) = x
  rw [evaluateFunctorAt_functorVertex, SSet.yonedaEquiv_symm_app]
  have h : stdSimplex.objEquiv.{u} (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by decide
  rw [h]
  exact e.src_eq

private lemma pullback_vertex_ext {A C B : SSet.{u}} (p : A ⟶ B) (q : C ⟶ B)
    {s t : (pullback p q) _⦋0⦌}
    (h₀ : (pullback.fst p q).app (Opposite.op ⦋0⦌) s =
      (pullback.fst p q).app (Opposite.op ⦋0⦌) t)
    (h₁ : (pullback.snd p q).app (Opposite.op ⦋0⦌) s =
      (pullback.snd p q).app (Opposite.op ⦋0⦌) t) : s = t := by
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₀]
  · rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, h₁]

/-- 概要：始点と基底の path を指定すると cocartesian な path の頂点が存在する。
方針：基底の関手頂点を辺に戻し、cocartesian fibration の辺の持ち上げを使う。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.4 の coherent な輸送の零次元。 -/
lemma cocartesianPathSpaceSource_surjective {E B : SSet.{u}} (p : E ⟶ B)
    [CocartesianHornFibration p] :
    Function.Surjective ((cocartesianPathSpaceSource p).app (Opposite.op ⦋0⦌)) := by
  intro s
  let evB := evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let x := (pullback.fst p evB).app (Opposite.op ⦋0⦌) s
  let v := (pullback.snd p evB).app (Opposite.op ⦋0⦌) s
  have hsq : pullback.fst p evB ≫ p = pullback.snd p evB ≫ evB := pullback.condition
  have hs : p.app (Opposite.op ⦋0⦌) x = evB.app (Opposite.op ⦋0⦌) v :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hsq (Opposite.op ⦋0⦌)) s
  let d := intervalFunctorVertexTypedEdge v
  let d' : SSet.Truncated.Edge (X := (truncation 2).obj B)
      (p.app (Opposite.op ⦋0⦌) x)
      ((evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) v) :=
    { edge := d.edge
      src_eq := d.src_eq.trans hs.symm
      tgt_eq := d.tgt_eq }
  obtain ⟨y, e, hp, he⟩ := CocartesianHornFibration.exists_lift (p := p) x _ d'
  refine ⟨cocartesianPathVertex p e he, ?_⟩
  apply pullback_vertex_ext p evB
  · have hh := ConcreteCategory.congr_hom (NatTrans.congr_app
        (cocartesianPathSpaceSource_fst p) (Opposite.op ⦋0⦌)) (cocartesianPathVertex p e he)
    exact hh.trans (cocartesianPathVertex_zero p e he)
  · have hh := ConcreteCategory.congr_hom (NatTrans.congr_app
        (cocartesianPathSpaceSource_snd p) (Opposite.op ⦋0⦌)) (cocartesianPathVertex p e he)
    apply hh.trans
    change ((ihom (Δ[1] : SSet.{u})).map p).app (Opposite.op ⦋0⦌)
      (functorVertex (SSet.yonedaEquiv.symm e.edge)) = v
    apply (functorVertexEquiv Δ[1] B).symm.injective
    change (SSet.yonedaEquiv.symm e.edge) ≫ p = (functorVertexEquiv Δ[1] B).symm v
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hp

end SerrePositivity.InfinityCategories
