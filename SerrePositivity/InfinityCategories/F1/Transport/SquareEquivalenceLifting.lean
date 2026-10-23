module

public import SerrePositivity.InfinityCategories.F1.Transport.SquareSpecifiedLifting
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.F1.Transport.SquareEdgeInvariance
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFirstVertex

/-!
概要：可逆な分類図式の辺を持つ四角形を単射な底変換に沿って持ち上げる。
方針：可逆な分類図式の辺を先に延長し、相対内部 Hom で全空間側を延長する。
規約：始点と制限先の辺はともに厳密に固定する。
使われ方：Kerodon Lemma 5.6.8.10、制限の一次の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単射への四角形の制限は可逆な分類図式を持つ辺を指定始点から持ち上げる。
方針：分類図式の可逆な辺を延長し、指定した延長を被覆する四角形を持ち上げる。
規約：制限先の四角形の辺をそのまま保つ。
使われ方：Kerodon Lemma 5.6.8.10、表現の制限の一次のホーン充填。 -/
lemma transportSquareRestriction_liftInvertibleDiagramEdge {E B D : SSet.{u + 1}}
    (p : E ⟶ B) (g : D ⟶ B) [Mono g] (S : LeftTransportSquare p)
    {y : (transportSquareSpace (pullback.snd p g)) _⦋0⦌}
    (e : SSet.Edge ((transportSquareRestriction p g).app _ (transportSquareVertex S)) y)
    (he : IsInvertibleEdge (e.map (transportSquareDiagram (pullback.snd p g)))) :
    ∃ L : (Δ[1] : SSet.{u + 1}) ⟶ transportSquareSpace p,
      stdSimplex.δ 1 ≫ L = SSet.yonedaEquiv.symm (transportSquareVertex S) ∧
      L ≫ transportSquareRestriction p g = SSet.yonedaEquiv.symm e.edge ∧
      IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (L ≫ transportSquareDiagram p))) := by
  let G := (functorVertexEquiv D SpaceInfinity).symm
    ((transportSquareDiagram (pullback.snd p g)).app _ y)
  have hG : functorVertex G = (transportSquareDiagram (pullback.snd p g)).app _ y :=
    (functorVertexEquiv D SpaceInfinity).apply_symm_apply _
  have hsrc : (transportSquareDiagram (pullback.snd p g)).app _
      ((transportSquareRestriction p g).app _ (transportSquareVertex S)) =
        functorVertex (g ≫ S.diagram) := by
    rw [transportSquareRestriction_vertex, transportSquareVertex_diagram]
    rfl
  let eD := (e.map (transportSquareDiagram (pullback.snd p g))).ofEq hsrc hG.symm
  have heD : IsInvertibleEdge eD := (isInvertibleEdge_congr (show eD.edge =
    (e.map (transportSquareDiagram (pullback.snd p g))).edge from rfl)).mpr he
  obtain ⟨F', l, hl, hli⟩ := pre_liftInvertibleEdge_source g S.diagram G eD heD
  let a := SSet.yonedaEquiv.symm (transportSquareVertex S)
  let b := SSet.yonedaEquiv.symm e.edge
  let F := SSet.yonedaEquiv.symm l.edge
  have sq : CommSq a (stdSimplex.δ (1 : Fin 2)) (transportSquareRestriction p g) b := ⟨by
    dsimp only [a, b]
    rw [SSet.yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]⟩
  have hF₀ : stdSimplex.δ 1 ≫ F = a ≫ transportSquareDiagram p := by
    dsimp only [F, a]
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, l.src_eq, SSet.yonedaEquiv_symm_comp,
      transportSquareVertex_diagram]
  have hFg : F ≫ (pre g).app SpaceInfinity =
      b ≫ transportSquareDiagram (pullback.snd p g) := by
    dsimp only [F, b]
    rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hl]
    rfl
  let r := Functor.PullbackObjObj.ofHasPullback internalHom
    (pullback.fst p g) pointedSpaceProjection
  have : LeftFibration r.π :=
    leftFibration_pullbackObjObjπ (pullback.fst p g) pointedSpaceProjection r
  have hv : scaffoldFirstVertex.{u + 1} 1 = stdSimplex.δ (1 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    apply stdSimplex.ext
    intro i
    fin_cases i
    rfl
  have : HasLiftingProperty (stdSimplex.δ (1 : Fin 2)) r.π := by
    rw [← hv]
    exact (scaffoldFirstVertex_leftAnodyne 1) r.π (LeftFibration.mem (p := r.π))
  obtain ⟨L, hL₀, hLg, hLD⟩ := exists_transportSquareLift_with_diagram p g (stdSimplex.δ 1)
    a b sq F hF₀ hFg r
  refine ⟨L, hL₀, hLg, ?_⟩
  have h : SSet.yonedaEquiv (L ≫ transportSquareDiagram p) = l.edge := by
    rw [hLD]
    exact Equiv.apply_symm_apply _ _
  exact (isInvertibleEdge_congr h).mpr hli

end SerrePositivity.InfinityCategories
