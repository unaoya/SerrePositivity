module

public import SerrePositivity.InfinityCategories.Core.IntervalBoundary
public import SerrePositivity.InfinityCategories.Core.PrecompositionRelativeLifting

/-!
概要：単射な前合成同値に沿う、両端固定の prism の延長。
方針：区間の境界への制限を内部 Hom の持ち上げ問題に移す。
規約：標準区間は第一因子、指定部分は第二因子に置く。
使われ方：相対 Kan 拡張の可逆 path による因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定部分の prism を両端を変えずに全体へ延長する。
方針：区間境界による前合成への右持ち上げを uncurry する。
規約：パラメータの包含は単射な前合成同値、標的のみ quasicategory。
使われ方：可逆 path の始点・終点と指定部分を同時に保つ延長。 -/
lemma exists_kanPrism_extension_of_precompositionEquivalence
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) [Mono i]
    (hi : IsPrecompositionEquivalence i) (f g : B ⟶ X)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = i ≫ f)
    (h₁ : prismEndpoint 1 A ≫ H = i ≫ g) :
    ∃ G : (Δ[1] : SSet.{u}) ⊗ B ⟶ X,
      (Δ[1] ◁ i) ≫ G = H ∧ prismEndpoint 0 B ≫ G = f ∧
        prismEndpoint 1 B ≫ G = g := by
  have := hi.hasLiftingProperty_pre (boundary 1).ι X
  let sq : CommSq (curry H) i ((pre (boundary 1).ι).app X)
      (curry (intervalBoundaryDiagram f g)) := ⟨by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_natural_left, uncurry_curry,
      intervalBoundaryDiagram_restrict, h₀, h₁, intervalBoundaryDiagram_naturality]⟩
  have hb : ((boundary 1).ι ▷ B) ≫ uncurry sq.lift = intervalBoundaryDiagram f g := by
    have h := congrArg uncurry sq.fac_right
    rw [uncurry_pre_app, uncurry_curry] at h
    exact h
  refine ⟨uncurry sq.lift, ?_, ?_, ?_⟩
  · have h := congrArg uncurry sq.fac_left
    rw [uncurry_natural_left, uncurry_curry] at h
    exact h
  · rw [← intervalBoundaryEndpoint_ι, Category.assoc, hb, intervalBoundaryDiagram_zero]
  · rw [← intervalBoundaryEndpoint_ι, Category.assoc, hb, intervalBoundaryDiagram_one]

end SerrePositivity.InfinityCategories.F1B
