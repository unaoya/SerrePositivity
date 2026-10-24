module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftBoundaryExtension
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberTranspose

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
      (SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ (SerrePositivity.InfinityCategories.F1B.functorTranspose a) c).val) x).val =
      (leftKanCanonicalCocone δ
        ((functorVertexEquiv C D).symm (a.app (Opposite.op ⦋0⦌) x)) c).val := by
  apply functorVertex_injective
  rw [kanCoconeFamilyAt_vertex]
  change (SerrePositivity.InfinityCategories.F1B.functorTranspose (kanLeftCanonicalCoconeMap δ c ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose a)).app
    (Opposite.op ⦋0⦌) x = functorVertex _
  rw [SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]
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
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U) (n : ℕ)
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
  have hFA : SerrePositivity.InfinityCategories.F1B.functorTranspose d ≫ (pre (boundary (n + 1)).ι).app D =
      δ ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose a := by
    have h := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose had
    rw [SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left] at h
    exact h.symm
  have hFG : SerrePositivity.InfinityCategories.F1B.functorTranspose d ≫ (ihom (Δ[n + 1] : SSet.{u})).map U =
      δ ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose g := by
    have h := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose hdg
    rw [kanFunctorTranspose_postcomp, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right] at h
    exact h
  have hAG : SerrePositivity.InfinityCategories.F1B.functorTranspose a ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
      SerrePositivity.InfinityCategories.F1B.functorTranspose g ≫ (pre (boundary (n + 1)).ι).app E := by
    have h := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose hag
    rw [kanFunctorTranspose_postcomp, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left] at h
    exact h
  have hlocal : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanCoconeFamilyAt
      (SerrePositivity.InfinityCategories.F1B.functorTranspose (leftKanCanonicalCocone δ (SerrePositivity.InfinityCategories.F1B.functorTranspose a) c).val)
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
    (SerrePositivity.InfinityCategories.F1B.functorTranspose d) (SerrePositivity.InfinityCategories.F1B.functorTranspose a) (SerrePositivity.InfinityCategories.F1B.functorTranspose g) hFA hFG hAG hlocal
  refine ⟨SerrePositivity.InfinityCategories.F1B.functorTranspose H, ?_, ?_, ?_⟩
  · rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right, hHA, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]
  · rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, hHF, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]
  · rw [← kanFunctorTranspose_postcomp, hHG, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]

end SerrePositivity.InfinityCategories.F1B
