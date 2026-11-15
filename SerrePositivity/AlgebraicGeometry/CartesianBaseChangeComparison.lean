module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelCartesian

/-!
概要：元の対象を保つ Cartesian 比較を、さらに後の係数段へ自然に移す。
方針：実際の pullback lift と、二射影・Cartesian 正方形の貼り合わせの消去。
規約：係数射の因子化を保持し、単射性や忠実平坦性を仮定しない。
使われ方：G2 の元のチャート・重なりと後段の実際の貼り合わせとの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X Y T S B : Scheme.{u}}

/-- 元の Cartesian 比較を、元の源を保ったまま後の係数段へ移す。 -/
def cartesianBaseChangeComparison (a : X ⟶ Y) (x : X ⟶ T) (p : Y ⟶ S) (g : T ⟶ S)
    (ha : IsPullback a x p g) (e : T ⟶ B) (δ : B ⟶ S) (h : e ≫ δ = g) : X ⟶ pullback δ p :=
  pullback.lift (x ≫ e) a (by rw [Category.assoc, h, ha.w])

/-- 元の比較への射影はそのまま元の射。 -/
@[reassoc (attr := simp)] theorem cartesianBaseChangeComparison_snd
    (a : X ⟶ Y) (x : X ⟶ T) (p : Y ⟶ S) (g : T ⟶ S)
    (ha : IsPullback a x p g) (e : T ⟶ B) (δ : B ⟶ S) (h : e ≫ δ = g) :
    cartesianBaseChangeComparison a x p g ha e δ h ≫ pullback.snd δ p = a := by
  simp [cartesianBaseChangeComparison]

/-- 元の源の構造射と後段の係数射との合成が基底座標。 -/
@[reassoc (attr := simp)] theorem cartesianBaseChangeComparison_fst
    (a : X ⟶ Y) (x : X ⟶ T) (p : Y ⟶ S) (g : T ⟶ S)
    (ha : IsPullback a x p g) (e : T ⟶ B) (δ : B ⟶ S) (h : e ≫ δ = g) :
    cartesianBaseChangeComparison a x p g ha e δ h ≫ pullback.fst δ p = x ≫ e := by
  simp [cartesianBaseChangeComparison]

/-- 元の源を保った後段への比較も Cartesian。 -/
theorem isPullback_cartesianBaseChangeComparison
    (a : X ⟶ Y) (x : X ⟶ T) (p : Y ⟶ S) (g : T ⟶ S)
    (ha : IsPullback a x p g) (e : T ⟶ B) (δ : B ⟶ S) (h : e ≫ δ = g) :
    IsPullback (cartesianBaseChangeComparison a x p g ha e δ h) x (pullback.fst δ p) e := by
  have houter : IsPullback
      (cartesianBaseChangeComparison a x p g ha e δ h ≫ pullback.snd δ p) x p (e ≫ δ) := by
    simpa only [cartesianBaseChangeComparison_snd, h] using ha
  exact houter.of_right (cartesianBaseChangeComparison_fst a x p g ha e δ h)
    (IsPullback.of_hasPullback δ p).flip

section Naturality
variable {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
  (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (x₁ : X₁ ⟶ T) (x₂ : X₂ ⟶ T)
  (p₁ : Y₁ ⟶ S) (p₂ : Y₂ ⟶ S) (g : T ⟶ S)
  (h₁ : IsPullback a₁ x₁ p₁ g) (h₂ : IsPullback a₂ x₂ p₂ g)
  (e : T ⟶ B) (δ : B ⟶ S) (he : e ≫ δ = g)
  (f : X₁ ⟶ X₂) (r : Y₁ ⟶ Y₂) (hr : r ≫ p₂ = p₁)
  (hf : a₁ ≫ r = f ≫ a₂) (hx : x₁ = f ≫ x₂)

include hf hx

/-- 元の模型間の可換式は、後段への実際の比較の自然性を与える。 -/
theorem cartesianBaseChangeComparison_naturality :
    cartesianBaseChangeComparison a₁ x₁ p₁ g h₁ e δ he ≫ baseChangedModelArrow δ p₁ p₂ r hr =
      f ≫ cartesianBaseChangeComparison a₂ x₂ p₂ g h₂ e δ he := by
  apply pullback.hom_ext
  · simp [Category.assoc, hx]
  · simpa only [Category.assoc, baseChangedModelArrow_snd, cartesianBaseChangeComparison_snd_assoc,
      cartesianBaseChangeComparison_snd] using hf

/-- 元の構造射を保つ自然性の正方形は、後段で Cartesian。 -/
theorem isPullback_cartesianBaseChangeComparison_square :
    IsPullback (cartesianBaseChangeComparison a₁ x₁ p₁ g h₁ e δ he) f
      (baseChangedModelArrow δ p₁ p₂ r hr) (cartesianBaseChangeComparison a₂ x₂ p₂ g h₂ e δ he) := by
  have houter : IsPullback (cartesianBaseChangeComparison a₁ x₁ p₁ g h₁ e δ he)
      (f ≫ x₂) (baseChangedModelArrow δ p₁ p₂ r hr ≫ pullback.fst δ p₂) e := by
    rw [baseChangedModelArrow_fst, ← hx]
    exact isPullback_cartesianBaseChangeComparison a₁ x₁ p₁ g h₁ e δ he
  exact houter.of_bot
    (cartesianBaseChangeComparison_naturality a₁ a₂ x₁ x₂ p₁ p₂ g h₁ h₂ e δ he f r hr hf hx)
    (isPullback_cartesianBaseChangeComparison a₂ x₂ p₂ g h₂ e δ he)

end Naturality
end SerrePositivity.AlgebraicGeometry
