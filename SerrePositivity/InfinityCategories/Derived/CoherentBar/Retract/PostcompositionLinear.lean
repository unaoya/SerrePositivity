module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.ShiftedHomCoordinates
/-!
概要：固定した全斉次 Hom への後合成を、基礎環上の線形写像として扱う。
方針：豊穣合成の tensor 表示からスカラー保存を示し、既存の加法性とまとめる。
規約：閉射の条件を課さず、始域・中間対象・終域と全次数を保持する。
使われ方：実境界の係数比較を有限係数和へ線形に延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarRetractHom_compose_smul_right {M N P : RightModule R D} {p q k : ℤ}
    (r : R) (g : (moduleHom R D N P).X q) (f : (moduleHom R D M N).X p)
    (hk : p + q = k) :
    compose R (x := M) (y := N) (z := P) g (r • f) hk =
      r • compose R (x := M) (y := N) (z := P) g f hk := by
  unfold compose forward
  rw [← TensorProduct.smul_tmul' (R := R) r f g]
  simp only [map_smul]
  exact smul_comm _ _ _

def dgBarRetractPostcompositionLinear {M N P : RightModule R D} {p q k : ℤ}
    (g : (moduleHom R D N P).X q) (hk : p + q = k) :
    (moduleHom R D M N).X p →ₗ[R] (moduleHom R D M P).X k where
  toFun f := compose R (x := M) (y := N) (z := P) g f hk
  map_add' f h := compose_add_right (A := R) (D := RightModule R D) g f h hk
  map_smul' r f := dgBarRetractHom_compose_smul_right R D r g f hk

end SerrePositivity.InfinityCategories
