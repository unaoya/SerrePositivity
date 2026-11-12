module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanTransportedKanPath
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanSpecifiedHomotopy

/-!
概要：指定有限 path の同時輸送を、元の境界全円柱を保つ Kan 置換内の正方形へ移す。
方針：有限模型の輸送を単位に沿って厳密に延長し、元の有限 path の射で前合成する。
規約：元の path への比較と、輸送先への全境界輸送を同時に保持する。
使われ方：一般 coherent filtered 引き戻しの標的側の同時有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二入力の同時輸送と整合する、有限 path 全体の Kan 置換内の正方形を構成。
方針：単射境界の有限輸送と指定円柱の Kan 延長を合成する。
規約：元の path への端点固定比較も保持。使われ方：標的引き戻し内のホモトピーの構成。 -/
lemma cospan_finite_kan_square {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (u : K ⟶ E) (v : K ⟶ D)
    (H₀ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H)) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ vertexFiber (f ≫ p) b,
      ∃ t : K ⟶ vertexFiber (g ≫ p) b, ∃ M : SSet.{u}, ∃ m : K ⨿ K ⟶ M,
      ∃ q : M ⟶ H, ∃ z : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj M,
      ∃ w : M ⟶ vertexFiber p b,
      ∃ Hu : SSet.Homotopy u (s ≫ vertexFiberι (f ≫ p) b),
      ∃ Hv : SSet.Homotopy v (t ≫ vertexFiberι (g ≫ p) b),
      ∃ G : SSet.Homotopy H₀.h (z ≫ continuousKanReplacement.map q),
      ∃ T : SSet.Homotopy (z ≫ continuousKanReplacement.map q)
        (z ≫ continuousKanReplacement.map (w ≫ vertexFiberι p b)),
        M.Finite ∧ Mono m ∧ m ≫ q = coprod.desc (u ≫ f) (v ≫ g) ∧
        cylinderBoundaryInclusion K ≫ z = m ≫ continuousKanReplacementUnit.app M ∧
        m ≫ w = coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
          (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ∧
        (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫ coprod.desc (u ≫ f) (v ≫ g) ≫
            continuousKanReplacementUnit.app H ∧
        (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ T.h =
          coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) ≫ continuousKanReplacementUnit.app H := by
  obtain ⟨b, s, t, M, m, q, z, w, Hu, Hv, Hq, G, hM, hm, hq, hz, hw, hHq, hG⟩ :=
    cospan_finite_path_transport p f g u v H₀
  obtain ⟨T, hT⟩ := continuousKanReplacement_specified_homotopy_precomp Hq
    (cylinderBoundaryInclusion K) m z hz
  refine ⟨b, s, t, M, m, q, z, w, Hu, Hv, G, T, hM, hm, hq, hz, hw, hG, ?_⟩
  rw [← Category.assoc, hHq] at hT
  exact hT

end SerrePositivity.InfinityCategories.F2
