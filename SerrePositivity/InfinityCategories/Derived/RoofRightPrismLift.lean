module
public import SerrePositivity.InfinityCategories.F1B.CofinalFixedRightPrism

/-! # 右ファイブレーション上の終端固定 prism

概要：任意の底の prism と指定終端図式を同時に持ち上げる。
方針：最後の一次ホーンと任意の単体集合の積の right anodyne 性を使う。
規約：底・終端を厳密に保つ。使われ方：有限屋根図式を共通 fiber へ輸送する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 右ファイブレーションは任意の prism を指定終端図式から持ち上げる。 -/
lemma roofRightFibration_lift_end_prism {K E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (f : K ⟶ E)
    (β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B)
    (hβ : f ≫ p = prismEndpoint 1 K ≫ β) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ K ⟶ E,
      prismEndpoint 1 K ≫ H = f ∧ H ≫ p = β := by
  have := rightAnodyneExtensions_point_whiskerRight K p (RightFibration.mem (p := p))
  have sq : CommSq (snd (horn 1 1 : SSet.{u}) K ≫ f) ((horn 1 1).ι ▷ K) p β := by
    constructor
    rw [Category.assoc, hβ, ← Category.assoc, ← cofinalLastHorn_prism_factorization]
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  have h := congrArg (fun g => hornOneLastSection K ≫ g) sq.fac_left
  simpa only [← Category.assoc, hornOneLastSection_ι, hornOneLastSection_snd,
    Category.id_comp] using h

end SerrePositivity.InfinityCategories
