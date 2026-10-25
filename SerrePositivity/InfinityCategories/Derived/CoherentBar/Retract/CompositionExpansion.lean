module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedOperators
/-!
概要：符号付き面和と prefix 和への斉次合成を有限和へ分配する。
方針：DGNerve の斉次合成の加法性・符号スカラー保存を、抽象対象の段階で適用する。
規約：始域・中間対象・終域と合成次数の等号を明示的に保持する。
使われ方：実 bar の正規化境界を二つの面和と相殺する prefix 和に分ける。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {M N P : C} {p q k : ℤ}

lemma dgBarRetract_compose_finite_sum_left {m n : ℕ}
    (a : Fin m → ℤˣ) (b : ℤˣ)
    (f : Fin m → GradedHom R N P q) (g : Fin n → GradedHom R N P q)
    (e : GradedHom R M N p) (hk : p + q = k) :
    compose R ((∑ i, a i • f i) + b • ∑ j, g j) e hk =
      (∑ i, a i • compose R (f i) e hk) + b • ∑ j, compose R (g j) e hk := by
  simp only [compose_add_left, compose_sum_left, compose_units_smul_left]

lemma dgBarRetract_compose_finite_sum_right {m n : ℕ}
    (a : Fin m → ℤˣ) (b : ℤˣ)
    (f : Fin m → GradedHom R M N p) (g : Fin n → GradedHom R M N p)
    (e : GradedHom R N P q) (hk : p + q = k) :
    compose R e ((∑ i, a i • f i) + b • ∑ j, g j) hk =
      (∑ i, a i • compose R e (f i) hk) + b • ∑ j, compose R e (g j) hk := by
  simp only [compose_add_right, compose_sum_right, compose_units_smul_right]

end SerrePositivity.InfinityCategories
