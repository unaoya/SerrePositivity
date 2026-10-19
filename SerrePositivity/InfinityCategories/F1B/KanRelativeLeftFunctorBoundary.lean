module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftBoundaryExtension
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFiberTranspose

/-!
概要：元の関手の族の相対境界延長を標準局所条件から構成する。
方針：標準余錐の転置と頂点評価を照合し、境界固定の厳密な存在を転置して戻す。
規約：元の図式・全境界・標的の全図式を等式で保つ。
使われ方：元の相対左 Kan 制限の始点境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準局所余錐の転置の頂点は元の関手頂点の標準余錐。
方針：余錐を与える射への前合成の自然性と二重転置を使う。
規約：図式の表示が異なっても全余錐の射として比較する。
使われ方：最初の関手頂点の標準局所条件を境界の局所充填へ渡す。 -/
lemma kanLeftCanonicalCocone_transpose_familyAt_val {K C A D : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) (a : A ⟶ (ihom C).obj D) (x : A _⦋0⦌) :
    (kanCoconeFamilyAt
      (kanFunctorTranspose (leftKanCanonicalCocone δ (kanFunctorTranspose a) c).val) x).val =
      (leftKanCanonicalCocone δ
        ((functorVertexEquiv C D).symm (a.app (Opposite.op ⦋0⦌) x)) c).val := by
  apply functorVertex_injective
  rw [kanCoconeFamilyAt_vertex]
  change (kanFunctorTranspose (kanLeftCanonicalCoconeMap δ c ≫ kanFunctorTranspose a)).app
    (Opposite.op ⦋0⦌) x = functorVertex _
  rw [kanFunctorTranspose_pre_left, kanFunctorTranspose_transpose]
  have h := (functorVertexEquiv C D).apply_symm_apply (a.app (Opposite.op ⦋0⦌) x)
  change functorVertex _ = a.app (Opposite.op ⦋0⦌) x at h
  exact congrArg (fun y ↦ ((pre (kanLeftCanonicalCoconeMap δ c)).app D).app
    (Opposite.op ⦋0⦌) y) h.symm

/-- 概要：元の相対左 Kan 関手で始まる境界は元と標的を固定して延長できる。
方針：族を転置し、最初の標準余錐の相対普遍性から境界固定の厳密な存在を使う。
規約：他の境界関手には相対左 Kan 条件を要求しない。
使われ方：元の関手圏の相対制限の正次元境界の充填。 -/
lemma exists_kanRelativeLeft_functor_relative_boundary_extension {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (U : D ⟶ E) (hU : KanEquivalenceLifting U) (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom C).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom K).obj D)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom C).obj E)
    (hdg : d ≫ (ihom K).map U = g ≫ (pre δ).app E)
    (had : a ≫ (pre δ).app D = (boundary (n + 1)).ι ≫ d)
    (hag : a ≫ (ihom C).map U = (boundary (n + 1)).ι ≫ g)
    (hfirst : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (leftKanCanonicalCocone δ
      ((functorVertexEquiv C D).symm (a.app (Opposite.op ⦋0⦌)
        ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)) c)) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom C).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧ f ≫ (pre δ).app D = d ∧ f ≫ (ihom C).map U = g := by
  have hFA : kanFunctorTranspose d ≫ (pre (boundary (n + 1)).ι).app D =
      δ ≫ kanFunctorTranspose a := by
    have h := congrArg kanFunctorTranspose had
    rw [kanFunctorTranspose_pre_right, kanFunctorTranspose_pre_left] at h
    exact h.symm
  have hFG : kanFunctorTranspose d ≫ (ihom (Δ[n + 1] : SSet.{u})).map U =
      δ ≫ kanFunctorTranspose g := by
    have h := congrArg kanFunctorTranspose hdg
    rw [kanFunctorTranspose_postcomp, kanFunctorTranspose_pre_right] at h
    exact h
  have hAG : kanFunctorTranspose a ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
      kanFunctorTranspose g ≫ (pre (boundary (n + 1)).ι).app E := by
    have h := congrArg kanFunctorTranspose hag
    rw [kanFunctorTranspose_postcomp, kanFunctorTranspose_pre_left] at h
    exact h
  have hlocal : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanCoconeFamilyAt
      (kanFunctorTranspose (leftKanCanonicalCocone δ (kanFunctorTranspose a) c).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩) := by
    intro c
    have hv := kanLeftCanonicalCocone_transpose_familyAt_val δ c a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩
    apply (kanIsRelativeColimitCone_congr U ?_ _ _ hv).2 (hfirst c)
    exact (kanCoconeFamilyAt _ _).property.symm.trans
      ((congrArg (fun f ↦ joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ≫ f) hv).trans
        (leftKanCanonicalCocone δ _ c).property)
  let sj := Functor.PullbackObjObj.ofHasPullback internalHom (boundary (n + 1)).ι U
  obtain ⟨H, hHF, hHA, hHG⟩ := exists_kanRelativeLeftBoundary_diagram_extension δ hδ U hU n sj
    (kanFunctorTranspose d) (kanFunctorTranspose a) (kanFunctorTranspose g) hFA hFG hAG hlocal
  refine ⟨kanFunctorTranspose H, ?_, ?_, ?_⟩
  · rw [← kanFunctorTranspose_pre_right, hHA, kanFunctorTranspose_transpose]
  · rw [← kanFunctorTranspose_pre_left, hHF, kanFunctorTranspose_transpose]
  · rw [← kanFunctorTranspose_postcomp, hHG, kanFunctorTranspose_transpose]

end SerrePositivity.InfinityCategories.F1B
