module

public import SerrePositivity.InfinityCategories.F2.RelativePathModelTransport
public import SerrePositivity.InfinityCategories.F2.RelativePathInputsTransport

/-!
概要：元の境界引き戻し射・二入力・有限 path 模型本体を全相対境界円柱を保って同時輸送する。
方針：底と入力の輸送を構成し、全境界の円柱を貼って標的模型を相対的に持ち上げる。
規約：輸送先は元の同じ頂点の値。追加の輸送や境界充填は仮定しない。
使われ方：境界付きの指定 Kan path の有限模型を元の値へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：境界の元の引き戻し射と全有限模型を、全円柱を保って元の同じ値へ同時輸送できる。
方針：共通底の収縮、境界固定の入力輸送、全相対境界の貼り合わせと相対持ち上げを合成する。
規約：元の全境界とその輸送を保持。使われ方：標的側の相対有限検出の模型輸送。 -/
lemma exists_relativePathFiniteModelTransport {K M E D H B : SSet.{u}}
    [K.Finite] [M.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (A : K.Subcomplex)
    (u : K ⟶ E) (v : K ⟶ D) (a : (A : SSet.{u}) ⟶ fiberwiseIntervalPullback p f g)
    (hu : A.ι ≫ u = a ≫ fiberwiseIntervalPullbackLeft p f g)
    (hv : A.ι ≫ v = a ≫ fiberwiseIntervalPullbackRight p f g)
    (m : relativePathBoundaryShape A ⟶ M) [Mono m] (q : M ⟶ H)
    (hk : (relativePathBoundarySide A ≫ m) ≫ q = fiberwisePullbackPathPrism p f g a)
    (he : (relativePathBoundaryEnds A ≫ m) ≫ q = intervalBoundaryDiagram (u ≫ f) (v ≫ g)) :
    ∃ d : RelativePathInputTransportData p f g A u v a m q,
      ∃ w : M ⟶ vertexFiber p d.vertex, m ≫ w = relativePathTransportTargetFiber d ∧
      ∃ G : SSet.Homotopy q (w ≫ vertexFiberι p d.vertex),
        (m ▷ (Δ[1] : SSet.{u})) ≫ G.h = (relativePathBoundaryTransportHomotopy d hk he).h ∧
        G.h ≫ p = d.modelBase.h := by
  have h₀ : (relativePathBoundaryEndpoint A 0 ≫ m) ≫ q = u ≫ f := by
    have h := congrArg (fun r ↦ intervalBoundaryEndpoint 0 K ≫ r) he
    simpa only [relativePathBoundaryEndpoint, Category.assoc, intervalBoundaryDiagram_zero] using h
  have h₁ : (relativePathBoundaryEndpoint A 1 ≫ m) ≫ q = v ≫ g := by
    have h := congrArg (fun r ↦ intervalBoundaryEndpoint 1 K ≫ r) he
    simpa only [relativePathBoundaryEndpoint, Category.assoc, intervalBoundaryDiagram_one] using h
  obtain ⟨d⟩ := exists_relativePathInputTransportData p f g A u v a hu hv m q hk h₀ h₁
  obtain ⟨w, hw, G, hG, hGp⟩ := relativePath_model_transport p f g A u v a m q d hk he
  exact ⟨d, w, hw, G, hG, hGp⟩

end SerrePositivity.InfinityCategories.F2
