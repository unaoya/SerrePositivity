module
public import SerrePositivity.InfinityCategories.Derived.DGFourLastHornRefinementFiller
public import SerrePositivity.InfinityCategories.Derived.DGVerdierTriangleCommonSource

/-! # 一つの追加実閉分母による四次ホーン有限族の同時実充填

概要：共通化済みの残差原始元の全てを、細分した実ホーンの全充填へ渡す。
方針：各原始元の二未知解と米田表示を使い、元の零面を厳密に保持する。
規約：共通分母は実辺の等式で記録。使われ方：実二単体有限族の高次整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
variable {P : Set D} {a : D} {m : ℕ}
variable {σ : Fin m → ((Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D)}
variable (T : DGFourLastHornFiniteRefinement P a σ)

/-- 同じ追加実閉分母後の各ホーンを全体として充填する実写像。 -/
def DGFourLastHornFiniteRefinement.filler (i : Fin m) : Δ[4] ⟶ dgNerve A D :=
  (T.residuals i).solution.extension

/-- 各実充填は、同じ細分ホーンの全指定面を厳密に延長する。 -/
lemma DGFourLastHornFiniteRefinement.filler_fac (i : Fin m) :
    (horn 4 4).ι ≫ T.filler i =
      dgFourLastHornSourceRefinement (σ i) (T.residuals i).q (T.residuals i).s :=
  (T.residuals i).solution.fac

/-- 全実充填の零面は、元の指定零面のまま。 -/
lemma DGFourLastHornFiniteRefinement.filler_face0 (i : Fin m) :
    SSet.stdSimplex.δ (0 : Fin 5) ≫ T.filler i =
      horn.ι (4 : Fin 5) 0 (by decide) ≫ σ i :=
  dgFourLastHornSourceRefinement_filler_face0 (T.residuals i) (T.filler i) (T.filler_fac i)

variable [IsDGPretriangulated A D]

/-- 共通始対象・実最後分母を持つ有限族は、一つの追加分母後に全て実充填できる。 -/
theorem dgFourLastHornFinite_exists_sourceRefinement_fillers
    (P : Set D) (a : D) {m : ℕ}
    (σ : Fin m → ((Λ[4, 4] : SSet.{max u v}) ⟶ dgNerve A D))
    (hsource : ∀ i, (HornData.knownData (σ i)).obj 0 = a)
    (hW : ∀ i, (dgClosedEdge A D (dgFourLastHornFinalClosed (σ i))).edge ∈
      dgVerdierEdges A D P) :
    ∃ T : DGFourLastHornFiniteRefinement P a σ, ∀ i, ∃ F : Δ[4] ⟶ dgNerve A D,
      (horn 4 4).ι ≫ F =
        dgFourLastHornSourceRefinement (σ i) (T.residuals i).q (T.residuals i).s ∧
      SSet.stdSimplex.δ (0 : Fin 5) ≫ F = horn.ι (4 : Fin 5) 0 (by decide) ≫ σ i := by
  obtain ⟨T⟩ := dgFourLastHornFiniteRefinement_nonempty P a σ hsource hW
  exact ⟨T, fun i => ⟨T.filler i, T.filler_fac i, T.filler_face0 i⟩⟩

variable (A D) {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}

/-- 同じ頂点錐の実二単体有限族には、一つの追加分母後に全ホーンの実充填がある。 -/
theorem dgVerdierTriangles_exists_refinedFillers
    (C : DGVerdierDiagramVertexCone A D P x f) {m : ℕ} (τ : Fin m → K _⦋2⦌)
    (G : ∀ j, ∀ i : Fin 3, Truncated.Edge.CompStruct
      (C.leg (K.δ 1 (K.δ i (τ j))))
      ((edgeOfSimplex (K.δ i (τ j))).map ((truncation 2).map f))
      (C.leg (K.δ 0 (K.δ i (τ j))))) :
    ∃ T : DGFourLastHornFiniteRefinement P
        (ForgetEnrichment.to (Complex A) C.denominator.obj.left)
        (fun j => dgVerdierDiagramTriangleHorn A D C (τ j) (G j)),
      ∀ j, ∃ F : Δ[4] ⟶ dgNerve A D,
        (horn 4 4).ι ≫ F = dgFourLastHornSourceRefinement
          (dgVerdierDiagramTriangleHorn A D C (τ j) (G j)) (T.residuals j).q (T.residuals j).s ∧
        SSet.stdSimplex.δ (0 : Fin 5) ≫ F = horn.ι (4 : Fin 5) 0 (by decide) ≫
          dgVerdierDiagramTriangleHorn A D C (τ j) (G j) := by
  obtain ⟨T⟩ := dgVerdierTrianglesResidualRefinement_nonempty A D C τ G
  exact ⟨T, fun j => ⟨T.filler j, T.filler_fac j, T.filler_face0 j⟩⟩

end SerrePositivity.InfinityCategories
