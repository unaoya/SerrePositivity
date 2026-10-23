module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackPathPrismHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredPathCollapseContraction
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LeftFibrationHomotopyTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberwisePullbackValueCoordinates

/-!
概要：元の境界引き戻し射と有限 path 模型の底を、同じ頂点へ整合的に輸送する。
方針：境界 path を潰した有限押し出し上で底を収縮し、境界の引き戻し射を持ち上げる。
規約：元の境界の全輸送と模型の底の全収縮を path 全体で厳密に一致させる。
使われ方：全相対境界を保つ有限 cospan 輸送の始点。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の境界引き戻し射と有限模型の底は、全 path 上で整合して同じ値へ輸送できる。
方針：底の押し出し収縮と引き戻し全空間の left fibration の持ち上げを合成する。
規約：境界の終点は元の値の引き戻し。使われ方：境界固定の二入力と標的の相対輸送。 -/
lemma fiberwisePullback_boundary_model_transport {A M E D H B : SSet.{u}}
    [A.Finite] [M.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)]
    (a : A ⟶ fiberwiseIntervalPullback p f g)
    (k : (Δ[1] : SSet.{u}) ⊗ A ⟶ M) (q : M ⟶ H)
    (hk : k ≫ q = fiberwisePullbackPathPrism p f g a) :
    ∃ b : B _⦋0⦌, ∃ t : A ⟶ intervalPullback (vertexFiberMap (f ≫ p) p f rfl b)
      (vertexFiberMap (g ≫ p) p g rfl b),
      ∃ Hq : SSet.Homotopy (q ≫ p) (SSet.const b),
      ∃ L : SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b),
        (k ▷ (Δ[1] : SSet.{u})) ≫ Hq.h =
          (snd (Δ[1] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫
            L.h ≫ fiberwiseIntervalPullbackProjection p f g := by
  have hb : k ≫ (q ≫ p) =
      snd (Δ[1] : SSet.{u}) A ≫ a ≫ fiberwiseIntervalPullbackProjection p f g := by
    rw [← Category.assoc, hk, fiberwisePullbackPathPrism_projection]
  obtain ⟨b, Hq, J, hJ⟩ := exists_nullHomotopy_with_collapsed_path k (q ≫ p)
    (a ≫ fiberwiseIntervalPullbackProjection p f g) hb
  obtain ⟨v, L₀, hL₀⟩ := leftFibration_transport_along_nullHomotopy
    (fiberwiseIntervalPullbackProjection p f g) a b J
  let e := fiberwisePullbackFiberIso p f g b
  let t := v ≫ e.hom
  have ht : t ≫ fiberwisePullbackValueToTotal p f g b =
      v ≫ vertexFiberι (fiberwiseIntervalPullbackProjection p f g) b := by
    change (v ≫ e.hom) ≫ (e.inv ≫ _) = _
    rw [Category.assoc, e.hom_inv_id_assoc]
  let L : SSet.Homotopy a (t ≫ fiberwisePullbackValueToTotal p f g b) :=
    { h := L₀.h
      h₀ := L₀.h₀
      h₁ := by
        change SSet.ι₁ ≫ L₀.h = t ≫ fiberwisePullbackValueToTotal p f g b
        rw [L₀.h₁, ht]
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨b, t, Hq, L, ?_⟩
  change (k ▷ (Δ[1] : SSet.{u})) ≫ Hq.h =
    (snd (Δ[1] : SSet.{u}) A ▷ (Δ[1] : SSet.{u})) ≫
      L₀.h ≫ fiberwiseIntervalPullbackProjection p f g
  rw [hL₀]
  exact hJ

end SerrePositivity.InfinityCategories.F2
