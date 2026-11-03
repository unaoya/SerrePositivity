module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanMonicFiberTransport
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.MonicFiniteHomotopyApproximation

/-!
概要：標的の指定有限 path を、二入力の輸送と全境界円柱を保持して共通値へ移す。
方針：単射境界の有限 path 近似を作り、二入力の輸送を標的の境界へ指定して相対輸送する。
規約：元の指定 path への境界固定の比較円柱を保存する。
使われ方：一般 coherent filtered 引き戻し比較の標的側の有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限二入力と元の指定 path の有限模型を、境界を保って同じ底の値へ移せる。
方針：境界単射の有限近似と指定境界円柱を保つ cospan の相対輸送を合成する。
規約：元の path への全比較円柱は両端上で時間定値。使われ方：標的側の有限三座標の検出。 -/
lemma cospan_finite_path_transport {K E D H B : SSet.{u}}
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
      ∃ Hq : SSet.Homotopy q (w ≫ vertexFiberι p b),
      ∃ G : SSet.Homotopy H₀.h (z ≫ continuousKanReplacement.map q),
        M.Finite ∧ Mono m ∧ m ≫ q = coprod.desc (u ≫ f) (v ≫ g) ∧
        cylinderBoundaryInclusion K ≫ z = m ≫ continuousKanReplacementUnit.app M ∧
        m ≫ w = coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
          (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ∧
        (m ▷ (Δ[1] : SSet.{u})) ≫ Hq.h = coprodCylinderMap (Hu.h ≫ f) (Hv.h ≫ g) ∧
        (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫ coprod.desc (u ≫ f) (v ≫ g) ≫
            continuousKanReplacementUnit.app H := by
  obtain ⟨M, m, q, z, hM, hm, hq, hz, G, hG⟩ :=
    continuousKanReplacement_homotopy_monic_finite_approximation (u ≫ f) (v ≫ g) H₀
  have := hM
  have := hm
  obtain ⟨b, s, t, w, Hu, Hv, Hq, hw, hHq⟩ :=
    leftFibration_cospan_monic_fiber_transport p f g m q u v hq
  exact ⟨b, s, t, M, m, q, z, w, Hu, Hv, Hq, G, hM, hm, hq, hz, hw, hHq, hG⟩

end SerrePositivity.InfinityCategories.F2
