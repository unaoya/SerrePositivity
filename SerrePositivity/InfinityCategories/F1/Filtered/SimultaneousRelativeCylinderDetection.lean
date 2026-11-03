module

public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.Filtered.GluedMappedBoundaryTransport
public import SerrePositivity.InfinityCategories.F1B.FilteredExchange.MappedBoundaryKanComparison
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.MonicAnchoredFiniteApproximation

/-!
概要：任意の有限 Kan 二入力を、共通の元の境界円柱を保って同じ元の fiber で検出する。
方針：単射有限近似を共通境界で貼り、同時輸送と相対 Kan 反映を合成する。
規約：二入力の比較円柱の制限は元の共通円柱の像に厳密に一致。
使われ方：Kan 引き戻し比較の任意の標的射への相対有限拡張。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：共通境界の全輸送を保持する、任意の有限 Kan 二入力の同時検出。
方針：単射有限近似・境界先行輸送・相対反映の構成を合成する。
規約：元の二入力の存在を仮定しない。使われ方：相対 Kan 引き戻し比較の入力輸送。 -/
lemma continuousKanLeftFibration_pair_relative_cylinder_detection {K R E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : R ⟶ B) [LeftFibration p] (q : E ⟶ B) [LeftFibration q]
    (r : D ⟶ B) [LeftFibration r] (c : R ⟶ E) (d : R ⟶ D)
    (hc : c ≫ q = p) (hd : d ≫ r = p) (A : K.Subcomplex) (a : (A : SSet.{u}) ⟶ R)
    (u : K ⟶ continuousKanReplacement.obj E) (v : K ⟶ continuousKanReplacement.obj D)
    (hu : (a ≫ c) ≫ continuousKanReplacementUnit.app E = A.ι ≫ u)
    (hv : (a ≫ d) ≫ continuousKanReplacementUnit.app D = A.ι ≫ v) :
    ∃ b : B _⦋0⦌, ∃ t : (A : SSet.{u}) ⟶ vertexFiber p b,
      ∃ s : K ⟶ vertexFiber q b, ∃ w : K ⟶ vertexFiber r b,
      A.ι ≫ s = t ≫ vertexFiberMap p q c hc b ∧
      A.ι ≫ w = t ≫ vertexFiberMap p r d hd b ∧
      ∃ T : SSet.Homotopy a (t ≫ vertexFiberι p b),
      ∃ U : SSet.Homotopy u (s ≫ vertexFiberι q b ≫ continuousKanReplacementUnit.app E),
      ∃ V : SSet.Homotopy v (w ≫ vertexFiberι r b ≫ continuousKanReplacementUnit.app D),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h = T.h ≫ c ≫ continuousKanReplacementUnit.app E ∧
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h = T.h ≫ d ≫ continuousKanReplacementUnit.app D := by
  obtain ⟨M, m, f, z, hM, hm, hf, hz, U₀, hU₀⟩ :=
    continuousKanReplacement_monic_anchored_finite_approximation A.ι (a ≫ c) u hu
  obtain ⟨N, n, g, z', hN, hn, hg, hz', V₀, hV₀⟩ :=
    continuousKanReplacement_monic_anchored_finite_approximation A.ι (a ≫ d) v hv
  let := hM
  let := hN
  let := hm
  let := hn
  obtain ⟨b, t, s₀, w₀, hs₀, hw₀, T, G, H, hG, hH⟩ :=
    leftFibration_glued_mapped_boundary_transport p q r c d hc hd m n a f g hf hg
  have hU₀' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U₀.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ c ≫ continuousKanReplacementUnit.app E := by
    simpa only [Category.assoc] using hU₀
  have hV₀' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V₀.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ d ≫ continuousKanReplacementUnit.app D := by
    simpa only [Category.assoc] using hV₀
  obtain ⟨s, hs, U, hU⟩ := continuousKanReplacement_mapped_boundary_comparison
    p q c hc A a b t T m f hf s₀ hs₀ G hG z hz u U₀ hU₀'
  obtain ⟨w, hw, V, hV⟩ := continuousKanReplacement_mapped_boundary_comparison
    p r d hd A a b t T n g hg w₀ hw₀ H hH z' hz' v V₀ hV₀'
  exact ⟨b, t, s, w, hs, hw, T, U, V, hU, hV⟩

end SerrePositivity.InfinityCategories.F2
