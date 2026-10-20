module

public import SerrePositivity.InfinityCategories.F2.FiberwisePullbackOriginalInputRelativeDetection
public import SerrePositivity.InfinityCategories.F2.KanCospanRelativeBoundaryPath

/-!
概要：実際の境界可換式を持つ有限 Kan 引き戻し射を、元の境界円柱を保って一値で検出する。
方針：境界可換式から全 path を回収し、相対有限検出を適用する。
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
lemma fiberwisePullbackKanComparison_original_input_relative_detection_of_boundary
    {K E D H B : SSet.{u}} [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ fiberwiseIntervalPullbackRight p f g)
    (H₀ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H))
    (hb : A.ι ≫ kanCospanPoint f g u v H₀ = a ≫
      continuousKanReplacementUnit.app (fiberwiseIntervalPullback p f g) ≫
        fiberwisePullbackKanComparison p f g) :
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
  have ha := kanCospanPoint_relative_boundary_path p f g A.ι u v a H₀ hb
  exact fiberwisePullbackKanComparison_original_input_relative_detection p f g A u v a hu hv H₀ ha

end SerrePositivity.InfinityCategories.F2
