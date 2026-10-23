module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedTransportPrismFamily
public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence

/-!
概要：指定面と部分パラメーター上の選択を保つ coherent な高次 transport の共同延長。
方針：空間値の図式を先に延長し、同じ底の上へ pointed な持ち上げを延長する。
規約：面の包含は inner anodyne、パラメーターの包含は任意の単射。
使われ方：三重以上の合成の図式と比較を同時に構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：部分的に指定した高次の空間値図式と pointed 比較を共同で厳密に延長する。
方針：内部 Hom の inner anodyne 制限の trivial Kan 性と pointed lift の相対延長を使う。
規約：既に選んだ面と部分パラメーター上の両図式を選び直さない。
使われ方：境界固定の高次 coherence の帰納的な構成。 -/
lemma exists_pointedTransportHigher_extension
    {A C E B K L : SSet.{u + 1}} (i : C ⟶ A) (hi : innerAnodyneExtensions i)
    (p : E ⟶ B) (j : L ⟶ K) [Mono j]
    (H₀ : (C ⊗ B) ⊗ K ⟶ SpaceInfinity.{u})
    (W₀ : (C ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hW₀ : W₀ ≫ pointedSpaceProjection = ((C ◁ p) ▷ K) ≫ H₀)
    (H₁ : (A ⊗ B) ⊗ L ⟶ SpaceInfinity.{u})
    (W₁ : (A ⊗ E) ⊗ L ⟶ PointedSpaceInfinity.{u})
    (hH₁ : ((i ▷ B) ▷ L) ≫ H₁ = ((C ⊗ B) ◁ j) ≫ H₀)
    (hW₁ : ((i ▷ E) ▷ L) ≫ W₁ = ((C ⊗ E) ◁ j) ≫ W₀)
    (hW₁p : W₁ ≫ pointedSpaceProjection = ((A ◁ p) ▷ L) ≫ H₁) :
    ∃ (H : (A ⊗ B) ⊗ K ⟶ SpaceInfinity.{u})
      (W : (A ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u}),
      ((i ▷ B) ▷ K) ≫ H = H₀ ∧
      ((A ⊗ B) ◁ j) ≫ H = H₁ ∧
      ((i ▷ E) ▷ K) ≫ W = W₀ ∧
      ((A ⊗ E) ◁ j) ≫ W = W₁ ∧
      W ≫ pointedSpaceProjection = ((A ◁ p) ▷ K) ≫ H := by
  have hiB : innerAnodyneExtensions (i ▷ B) := by
    intro X Y q hq
    exact hi.whiskerRight B q hq
  have : TrivialKanFibration ((pre (i ▷ B)).app SpaceInfinity.{u}) :=
    trivialKanFibration_pre_of_innerAnodyne (i ▷ B) hiB SpaceInfinity
  have := TrivialKanFibration.mem
    (p := (pre (i ▷ B)).app SpaceInfinity.{u}) j inferInstance
  have hs : curry H₁ ≫ (pre (i ▷ B)).app SpaceInfinity = j ≫ curry H₀ := by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_natural_left, uncurry_curry]
    exact hH₁
  let sq : CommSq (curry H₁) j ((pre (i ▷ B)).app SpaceInfinity) (curry H₀) := ⟨hs⟩
  let H := uncurry sq.lift
  have hH₀ : ((i ▷ B) ▷ K) ≫ H = H₀ := by
    dsimp only [H]
    rw [← uncurry_pre_app, sq.fac_right, uncurry_curry]
  have hHj : ((A ⊗ B) ◁ j) ≫ H = H₁ := by
    dsimp only [H]
    rw [← uncurry_natural_left, sq.fac_left, uncurry_curry]
  have hcomm : ((i ▷ E) ▷ K) ≫ ((A ◁ p) ▷ K) =
      ((C ◁ p) ▷ K) ≫ ((i ▷ B) ▷ K) := by
    apply SSet.hom_ext
    intro n
    rfl
  let D : PointedTransportPrismFamily (K := K) i p := {
    diagram := H
    boundary := W₀
    projection := by rw [hW₀, ← Category.assoc, hcomm, Category.assoc, hH₀] }
  have hiL : leftAnodyneExtensions i := by
    intro X Y q hq
    have : LeftFibration q := ⟨hq⟩
    exact hi q (InnerFibration.mem (q := q))
  have hW₁p' : W₁ ≫ pointedSpaceProjection =
      ((A ⊗ E) ◁ j) ≫ ((A ◁ p) ▷ K) ≫ D.diagram := by
    have hn : ((A ⊗ E) ◁ j) ≫ ((A ◁ p) ▷ K) =
        ((A ◁ p) ▷ L) ≫ ((A ⊗ B) ◁ j) := by
      apply SSet.hom_ext
      intro n
      rfl
    change _ = ((A ⊗ E) ◁ j) ≫ ((A ◁ p) ▷ K) ≫ H
    rw [← Category.assoc, hn, Category.assoc, hHj]
    exact hW₁p
  obtain ⟨W, hWj, hWi, hWp⟩ := D.exists_extension hiL j W₁ hW₁ hW₁p'
  exact ⟨H, W, hH₀, hHj, hWi, hWj, hWp⟩

end SerrePositivity.InfinityCategories
