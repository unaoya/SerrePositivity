module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanTransportedKanPath
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwisePullbackValueKanPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPointHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-!
概要：共通値へ輸送した Kan 引き戻し射を、元の値の実際の比較像へ戻す。
方針：端点固定の path 反映を元の包含で写し、引き戻し内で比較する。
規約：構成済み比較射の像を終点にする。
使われ方：一般 coherent filtered 引き戻し比較の有限持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：輸送した指定 path の Kan 引き戻し射は元の値の比較像へホモトピック。
方針：強変形 retract による端点固定反映を包含で写し、三座標を照合する。
規約：終点は元の構成済み比較。使われ方：元の一値での標的側の有限検出。 -/
lemma cospanTransportedKanPoint_reflection {K M E D H B : SSet.{u}}
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)
    (s : K ⟶ vertexFiber (f ≫ p) b) (t : K ⟶ vertexFiber (g ≫ p) b)
    (m : K ⨿ K ⟶ M) (z : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj M)
    (w : M ⟶ vertexFiber p b)
    (hz : cylinderBoundaryInclusion K ≫ z = m ≫ continuousKanReplacementUnit.app M)
    (hw : m ≫ w = coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
      (t ≫ vertexFiberMap (g ≫ p) p g rfl b))
    (H₁ : SSet.Homotopy ((s ≫ vertexFiberι (f ≫ p) b) ≫ f ≫ continuousKanReplacementUnit.app H)
      ((t ≫ vertexFiberι (g ≫ p) b) ≫ g ≫ continuousKanReplacementUnit.app H))
    (h₁ : H₁.h = z ≫ continuousKanReplacement.map (w ≫ vertexFiberι p b)) :
    ∃ L : SSet.Homotopy (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
      (t ≫ vertexFiberMap (g ≫ p) p g rfl b),
      Nonempty (SSet.Homotopy
        (kanCospanPoint f g (s ≫ vertexFiberι (f ≫ p) b) (t ≫ vertexFiberι (g ≫ p) b) H₁)
        (intervalPullbackHomotopyPoint (vertexFiberMap (f ≫ p) p f rfl b)
          (vertexFiberMap (g ≫ p) p g rfl b) s t L ≫
            fiberwisePullbackValueKanComparison p f g b)) := by
  have := vertexFiber_kanComplex_of_leftFibration p b
  obtain ⟨L, G, hG⟩ := cospanTransportedKanPath_reflection p f g b s t m z w hz hw
  have hn : continuousKanReplacementUnit.app (vertexFiber p b) ≫
      continuousKanReplacement.map (vertexFiberι p b) =
        vertexFiberι p b ≫ continuousKanReplacementUnit.app H :=
    (continuousKanReplacementUnit.naturality (vertexFiberι p b)).symm
  let H₀ := fiberwisePullbackValueKanPath p f g b s t L
  let G' : SSet.Homotopy H₀.h H₁.h :=
    { h := G.h ≫ continuousKanReplacement.map (vertexFiberι p b)
      h₀ := by
        change SSet.ι₀ ≫ (G.h ≫ continuousKanReplacement.map (vertexFiberι p b)) = H₀.h
        rw [← Category.assoc, G.h₀, Category.assoc, hn]
        rfl
      h₁ := by
        change SSet.ι₁ ≫ (G.h ≫ continuousKanReplacement.map (vertexFiberι p b)) = H₁.h
        rw [← Category.assoc, G.h₁, Category.assoc, ← Functor.map_comp, h₁]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  have hG' : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G'.h =
      fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫
        coprod.desc ((s ≫ vertexFiberι (f ≫ p) b) ≫ f)
          ((t ≫ vertexFiberι (g ≫ p) b) ≫ g) ≫ continuousKanReplacementUnit.app H := by
    change (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫
      (G.h ≫ continuousKanReplacement.map (vertexFiberι p b)) = _
    rw [← Category.assoc, hG]
    simp only [Category.assoc, hn]
    rw [← Category.assoc _ (vertexFiberι p b), coprod.desc_comp]
    simp only [Category.assoc, vertexFiberMap_ι]
  obtain ⟨J⟩ := kanCospanPoint_homotopy_of_fixed_boundary f g
    (s ≫ vertexFiberι (f ≫ p) b) (t ≫ vertexFiberι (g ≫ p) b) H₀ H₁ G' hG'
  refine ⟨L, ?_⟩
  rw [fiberwisePullbackValueKanComparison_point]
  exact (functorVertex_piZero_eq_iff_homotopy _ _).1
    (((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨J⟩).symm)

end SerrePositivity.InfinityCategories.F2
