module

public import SerrePositivity.KST.LocalizingInvariants.ArrowIsoRealization

/-!
概要：h 圏の指定可換四角形を、両端の成分まで指定した区間関手の同型へ実現する。
方針：両縦辺の代表を固定する実ホモトピーを選び、評価の Arrow 等号を保持する。
規約：端点の等号による輸送も含む。使われ方：d8 の元の二脚を保つ fiber 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma exists_arrowFunctorIso_with_endpoints {X : SSet.{u}} [Quasicategory X]
    {x y x' y' : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : Truncated.Edge (X := (truncation 2).obj X) x' y')
    (a : VertexIso x x') (b : VertexIso y y')
    (h : SSet.Truncated.HomotopyCategory.homMk f ≫ b.hom =
      a.hom ≫ SSet.Truncated.HomotopyCategory.homMk g) :
    ∃ e : FunctorIso (SSet.yonedaEquiv.symm f.edge) (SSet.yonedaEquiv.symm g.edge),
      Arrow.mk ((hoFunctor.map
        (evaluateFunctorAt (Y := X)
          (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk a.hom ∧
      Arrow.mk ((hoFunctor.map
        (evaluateFunctorAt (Y := X)
          (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk b.hom := by
  obtain ⟨s, hs⟩ := homotopyCategory_homMk_surjective x x' a.hom
  obtain ⟨t, ht⟩ := homotopyCategory_homMk_surjective y y' b.hom
  have hsi : IsInvertibleEdge s := by rw [IsInvertibleEdge, hs]; infer_instance
  have hti : IsInvertibleEdge t := by rw [IsInvertibleEdge, ht]; infer_instance
  obtain ⟨H, h₀, h₁⟩ := exists_arrowHomotopy_of_homMk_comm f g s t (by
    simpa only [hs, ht] using h)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) :=
    arrowHomotopy_isInvertible_of_endpointPaths H s t hsi hti h₀ h₁
  let e := asIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
  refine ⟨e, ?_, ?_⟩
  · have he := (homotopyEvaluationOfEndpoints_arrow H
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)))).trans
        (homotopyNatTransOfEndpoints_vertexPath_arrow H (stdSimplex.δ (1 : Fin 2)) s h₀)
    exact he.trans (congrArg Arrow.mk hs)
  · have he := (homotopyEvaluationOfEndpoints_arrow H
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)))).trans
        (homotopyNatTransOfEndpoints_vertexPath_arrow H (stdSimplex.δ (0 : Fin 2)) t h₁)
    exact he.trans (congrArg Arrow.mk ht)

end SerrePositivity.KST.LocalizingInvariants
