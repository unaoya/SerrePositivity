module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalRelativeBoundaryExtension
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberTranspose

/-!
概要：元の図式と U による全図式を固定する相対 join 関手の境界延長。
方針：関手の族を転置し、三つの指定を保つ大域境界延長を適用する。
規約：境界の最初の頂点の局所 U 余極限性だけを要求する。
使われ方：相対制限の始点境界充填と写像空間の制限定理。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標的の全関手も固定して相対 join 上の関手の境界を延長できる。
方針：局所余錐の頂点表示を同定して転置し、相対内部 Hom 上で大域的に組み立てる。
規約：元の図式、全境界、標的の全図式を厳密に保つ。
使われ方：普遍な相対図式の制限の正次元の境界充填。 -/
lemma exists_kanRelativeJoin_functor_relative_boundary_extension {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (relativeJoin p (𝟙 C))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom K).obj D)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (relativeJoin p (𝟙 C))).obj E)
    (hdg : d ≫ (ihom K).map U = g ≫ (pre (relativeJoinInl p (𝟙 C))).app E)
    (had : a ≫ (pre (relativeJoinInl p (𝟙 C))).app D = (boundary (n + 1)).ι ≫ d)
    (hag : a ≫ (ihom (relativeJoin p (𝟙 C))).map U = (boundary (n + 1)).ι ≫ g)
    (hfirst : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanRelativeJoinFiberCocone p c
      ((functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm
        (a.app (Opposite.op ⦋0⦌)
          ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩)))) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (relativeJoin p (𝟙 C))).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧
        f ≫ (pre (relativeJoinInl p (𝟙 C))).app D = d ∧
          f ≫ (ihom (relativeJoin p (𝟙 C))).map U = g := by
  have hFA : SerrePositivity.InfinityCategories.F1B.functorTranspose d ≫ (pre (boundary (n + 1)).ι).app D =
      relativeJoinInl p (𝟙 C) ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose a := by
    have h := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose had
    rw [SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left] at h
    exact h.symm
  have hFG : SerrePositivity.InfinityCategories.F1B.functorTranspose d ≫ (ihom (Δ[n + 1] : SSet.{u})).map U =
      relativeJoinInl p (𝟙 C) ≫ SerrePositivity.InfinityCategories.F1B.functorTranspose g := by
    have h := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose hdg
    rw [kanFunctorTranspose_postcomp, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right] at h
    exact h
  have hAG : SerrePositivity.InfinityCategories.F1B.functorTranspose a ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
      SerrePositivity.InfinityCategories.F1B.functorTranspose g ≫ (pre (boundary (n + 1)).ι).app E := by
    have h := congrArg SerrePositivity.InfinityCategories.F1B.functorTranspose hag
    rw [kanFunctorTranspose_postcomp, SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left] at h
    exact h
  have hlocal : ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanCoconeFamilyAt
      (SerrePositivity.InfinityCategories.F1B.functorTranspose (kanRelativeJoinFiberCocone p c (SerrePositivity.InfinityCategories.F1B.functorTranspose a)).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩) := by
    intro c
    have hv := kanRelativeJoinFiberCocone_transpose_familyAt_val p c a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), vertex_mem_boundary n 0⟩
    apply (kanIsRelativeColimitCone_congr U ?_ _ _ hv).2 (hfirst c)
    exact (kanCoconeFamilyAt _ _).property.symm.trans
      ((congrArg (fun f ↦ joinInl (vertexFiber p c) (Δ[0] : SSet.{u}) ≫ f) hv).trans
        (kanRelativeJoinFiberCocone p c _).property)
  let sj := Functor.PullbackObjObj.ofHasPullback internalHom (boundary (n + 1)).ι U
  obtain ⟨H, hHF, hHA, hHG⟩ := exists_kanGlobalRelativeBoundary_diagram_extension p U hU n sj
    (SerrePositivity.InfinityCategories.F1B.functorTranspose d) (SerrePositivity.InfinityCategories.F1B.functorTranspose a) (SerrePositivity.InfinityCategories.F1B.functorTranspose g) hFA hFG hAG hlocal
  refine ⟨SerrePositivity.InfinityCategories.F1B.functorTranspose H, ?_, ?_, ?_⟩
  · rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_right, hHA, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]
  · rw [← SerrePositivity.InfinityCategories.F1B.functorTranspose_pre_left, hHF, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]
  · rw [← kanFunctorTranspose_postcomp, hHG, SerrePositivity.InfinityCategories.F1B.functorTranspose_transpose]

end SerrePositivity.InfinityCategories.F1B
