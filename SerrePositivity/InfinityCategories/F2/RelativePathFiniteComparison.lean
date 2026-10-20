module

public import SerrePositivity.InfinityCategories.F2.RelativePathModelComparison
public import SerrePositivity.InfinityCategories.F2.RelativePathFiniteModelTransport
public import SerrePositivity.InfinityCategories.F2.RelativePathFiniteApproximation

/-!
概要：指定 Kan path の有限近似から元の値への相対比較を実際に構成する。
方針：全境界付き有限近似、同時輸送、元の値への反映と全円柱の合成。
規約：追加の輸送や充填を仮定しない。使われ方：一般 coherent 引き戻しの相対有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の全相対境界輸送を保つ、一値へ反映した path との比較が存在する。
方針：単射有限近似・相対輸送・境界固定反映の実際の構成を合成。
規約：一般の filtered 底、元の三全空間。使われ方：相対 Kan 引き戻し比較の正方形。 -/
lemma exists_relativePathFiniteComparison {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ fiberwiseIntervalPullbackRight p f g)
    (r₀ : (Δ[1] : SSet.{u}) ⊗ K ⟶ continuousKanReplacement.obj H)
    (hr₀ : prismEndpoint 0 K ≫ r₀ = (u ≫ f) ≫ continuousKanReplacementUnit.app H)
    (hr₁ : prismEndpoint 1 K ≫ r₀ = (v ≫ g) ≫ continuousKanReplacementUnit.app H)
    (hra : ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ r₀ =
      fiberwisePullbackPathPrism p f g a ≫ continuousKanReplacementUnit.app H) :
    ∃ (M : SSet.{u}) (m : relativePathBoundaryShape A ⟶ M) (q : M ⟶ H),
      ∃ d : RelativePathInputTransportData p f g A u v a m q,
      ∃ (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
        (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g)),
      ∃ (r : (Δ[1] : SSet.{u}) ⊗ K ⟶ vertexFiber p d.vertex)
        (hr : relativePathBoundaryι A ≫ r = relativePathTransportTargetFiber d),
      ∃ T : SSet.Homotopy r₀ (r ≫ vertexFiberι p d.vertex ≫ continuousKanReplacementUnit.app H),
        (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ T.h =
          (relativePathBoundaryTransportHomotopy d hk he).h ≫
            continuousKanReplacementUnit.app H ∧
        A.ι ≫ relativePathValuePoint d r hr = d.boundaryValue := by
  have h₀ : prismEndpoint 0 (A : SSet.{u}) ≫ fiberwisePullbackPathPrism p f g a =
      A.ι ≫ (u ≫ f) := by
    rw [fiberwisePullbackPathPrism_zero, ← Category.assoc, ← hu, Category.assoc]
  have h₁ : prismEndpoint 1 (A : SSet.{u}) ≫ fiberwisePullbackPathPrism p f g a =
      A.ι ≫ (v ≫ g) := by
    rw [fiberwisePullbackPathPrism_one, ← Category.assoc, ← hv, Category.assoc]
  obtain ⟨M, m, q, z, hM, hm, hmq, hz, U, hU⟩ :=
    continuousKanReplacement_relative_path_finite_approximation A (u ≫ f) (v ≫ g)
      (fiberwisePullbackPathPrism p f g a) h₀ h₁ r₀ hr₀ hr₁ hra
  let := hM
  let := hm
  have hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a := by
    rw [Category.assoc, hmq, relativePathBoundaryDiagram_side]
  have he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g) := by
    rw [Category.assoc, hmq, relativePathBoundaryDiagram_ends]
  obtain ⟨d, w, hw, G, hG, _⟩ :=
    exists_relativePathFiniteModelTransport p f g A u v a hu hv m q hk he
  have hU' : (relativePathBoundaryι A ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      CartesianMonoidalCategory.fst (relativePathBoundaryShape A) (Δ[1] : SSet.{u}) ≫
        m ≫ q ≫ continuousKanReplacementUnit.app H := by
    rw [hU, ← hmq, Category.assoc]
  obtain ⟨r, hr, T, hT, ha⟩ := relativePath_model_comparison p f g A u v a m q d hk he
    w hw G hG z hz r₀ U hU'
  exact ⟨M, m, q, d, hk, he, r, hr, T, hT, ha⟩

end SerrePositivity.InfinityCategories.F2
