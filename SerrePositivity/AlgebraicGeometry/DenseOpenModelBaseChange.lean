module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：模型上で同型な指定開の像を、元の基底上の稠密像へ渡す。
方針：開への制限の全射性と、実際の pullback の点の持ち上げを使う。
規約：Rydh Proposition 3.7。底変換全体の忠実平坦性は仮定しない。
使われ方：C02 で包絡する閉包の、基底への全射性の入力を作る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 指定開への制限が同型なら、その開の全点は元の射の像に入る。 -/
theorem range_contains_open_of_isIso_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] :
    ∀ y : Y, y ∈ U → y ∈ Set.range f := by
  intro y hy
  obtain ⟨x, hx⟩ := (f ∣_ U).surjective ⟨y, hy⟩
  refine ⟨x.1, ?_⟩
  calc
    f x.1 = ((f ∣_ U) ≫ U.ι) x := by rw [morphismRestrict_ι]; rfl
    _ = y := congrArg (fun z : U ↦ z.1) hx

/-- 模型の指定開の像と、元の基底上での稠密性は同じ底変換上の稠密像を与える。 -/
theorem denseRange_openRestriction_of_model_baseChange
    {Y Y₀ S S₀ : Scheme.{u}} {v : Y ⟶ Y₀} {p : Y ⟶ S}
    {p₀ : Y₀ ⟶ S₀} {g : S ⟶ S₀} (hY : IsPullback v p p₀ g)
    (U : S₀.Opens) (hU : ∀ s : S₀, s ∈ U → s ∈ Set.range p₀)
    (hDense : Dense (g ⁻¹ᵁ U : Set S)) :
    DenseRange ((p ⁻¹ᵁ g ⁻¹ᵁ U).ι ≫ p) := by
  have hsub : (g ⁻¹ᵁ U : Set S) ⊆ Set.range ((p ⁻¹ᵁ g ⁻¹ᵁ U).ι ≫ p) := by
    intro s hs
    obtain ⟨y₀, hy₀⟩ := hU (g s) hs
    obtain ⟨y, _, hy⟩ := Scheme.exists_preimage_of_isPullback hY y₀ s hy₀
    refine ⟨⟨y, ?_⟩, ?_⟩
    · change g (p y) ∈ U
      rw [hy]
      exact hs
    · change p y = s
      exact hy
  exact hDense.mono hsub

end SerrePositivity.AlgebraicGeometry
