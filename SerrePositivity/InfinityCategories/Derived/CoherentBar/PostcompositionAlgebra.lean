module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LastPostcomposition
/-!
概要：任意次数の後合成を、HA の符号付き削除項と切断項の差へ分配する。
方針：既存の斉次合成の線形性と全次数の結合則を使う。
規約：後合成射の次数を零に限定せず、閉性も仮定しない。
使われ方：混合 HA の元の単体側の和を、高次 Hom の Leibniz 項へ因数分解する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

lemma dgCoherentBarHom_postcompose_signed_difference {X M B Y : C} {p q r : ℤ}
    (f : GradedHom R X M p) (g : GradedHom R M B q)
    (e : GradedHom R X B (p + q)) (ρ : GradedHom R B Y r) (c : ℤˣ) :
    compose R ρ (c • (e - compose R g f rfl)) rfl =
      c • (compose R ρ e rfl -
        compose R (compose R ρ g rfl) f (show p + (q + r) = p + q + r by omega)) := by
  rw [DGNerve.compose_units_smul_right, DGNerve.compose_sub_right,
    DGNerve.compose_assoc_of_sum f g ρ rfl rfl rfl]

end SerrePositivity.InfinityCategories
