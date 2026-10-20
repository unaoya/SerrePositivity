module

public import SerrePositivity.InfinityCategories.F2.RelativePathFiniteComparison
public import SerrePositivity.InfinityCategories.F2.RelativePathKanPointComparison
public import SerrePositivity.InfinityCategories.F2.RelativePathKanComparisonRestriction

/-!
概要：元の二入力を持つ有限 Kan 引き戻し射を、元の境界円柱を保って一値で検出する。
方針：有限相対 path 比較を実際の Kan 引き戻し内へ移し、三座標で制限を照合する。
規約：元の境界値・全輸送円柱・構成済み比較射を保持。
使われ方：一般 coherent filtered 引き戻し比較の相対有限持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の二入力と境界を持つ有限標的射は、全境界輸送を保って元の一値で検出できる。
方針：全相対境界付きの近似・輸送・反映を実際の比較へ合成する。
規約：境界制限は厳密な射の等式。使われ方：一般 coherent 引き戻しの相対比較。 -/
lemma fiberwisePullbackKanComparison_original_input_relative_detection
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ fiberwiseIntervalPullbackRight p f g)
    (H₀ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H))
    (ha : ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h =
      fiberwisePullbackPathPrism p f g a ≫ continuousKanReplacementUnit.app H) :
    ∃ b : B _⦋0⦌,
      ∃ t : (A : SSet.{u}) ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b),
      ∃ w : K ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
        (vertexFiberMap (g ≫ p) p g rfl b), A.ι ≫ w = t ∧
      ∃ L : SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b),
      ∃ G : SSet.Homotopy (kanCospanPoint f g u v H₀)
        (w ≫ fiberwisePullbackValueKanComparison p f g b),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
          continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
            fiberwisePullbackKanComparison p f g := by
  have h₀ : prismEndpoint 0 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h =
      (u ≫ f) ≫ continuousKanReplacementUnit.app H := H₀.h₀
  have h₁ : prismEndpoint 1 K ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h =
      (v ≫ g) ≫ continuousKanReplacementUnit.app H := H₀.h₁
  obtain ⟨M, m, q, d, hk, he, r, hr, T, hT, ht⟩ :=
    exists_relativePathFiniteComparison p f g A u v a hu hv
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H₀.h) h₀ h₁ ha
  obtain ⟨G, hl, hr', hp⟩ := relativePath_kan_point_comparison d hk he r hr H₀ T hT
  exact ⟨d.vertex, d.boundaryValue, relativePathValuePoint d r hr, ht, d.boundaryHomotopy,
    G, relativePathKanComparison_restrict d hk he T.h hT G.h hl hr' hp⟩

end SerrePositivity.InfinityCategories.F2
