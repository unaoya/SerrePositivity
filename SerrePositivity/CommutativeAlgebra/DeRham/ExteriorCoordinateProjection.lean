module

public import SerrePositivity.CommutativeAlgebra.DeRham.ExteriorContraction

/-!
# 一座標を消す外冪の射影

## 概要
線形汎関数 d と d(a) = 1 のベクトル a に対し、x ↦ x − d(x)a の外冪を内部積で表す。

## 方針
外積単項式に対し、左内部積の公式と一次元の反交換則を使う。

## 規約
外冪の埋め込み先である外代数で公式を照合する。

## 使われ方
分冪 Poincaré 収縮と座標評価の照合。
-/

public noncomputable section

universe u

namespace SerrePositivity.DeRham

variable {k M : Type u} [CommRing k] [AddCommGroup M] [Module k M]

/-- 汎関数 d で測る a 成分を取り除く。 -/
def exteriorCoordinateProjection (d : Module.Dual k M) (a : M) : M →ₗ[k] M :=
  LinearMap.id - d.smulRight a

private theorem exteriorCoordinateProjection_mul
    (d : Module.Dual k M) (a b : M) (x : ExteriorAlgebra k M) :
    let C := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k M)) d
    let ι := ExteriorAlgebra.ι k
    ι (exteriorCoordinateProjection d a b) * (x - ι a * C x) =
      ι b * x - ι a * C (ι b * x) := by
  intro C ι
  have hb : ι b * ι a = -(ι a * ι b) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a)
  have hc : ι a * ι a = 0 := ExteriorAlgebra.ι_sq_zero a
  have hC : C (ι b * x) = d b • x - ι b * C x :=
    CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm k M)) d b x
  change ι (b - d b • a) * _ = _
  simp only [hC, map_sub, map_smul, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    ← mul_assoc, hb, hc, neg_mul, smul_zero, sub_zero]
  abel

private theorem exteriorCoordinateProjection_ιMulti
    (d : Module.Dual k M) (a : M) {j : ℕ} (v : Fin j → M) :
    let C := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k M)) d
    ExteriorAlgebra.ιMulti k j (exteriorCoordinateProjection d a ∘ v) =
      ExteriorAlgebra.ιMulti k j v - ExteriorAlgebra.ι k a * C (ExteriorAlgebra.ιMulti k j v) := by
  intro C
  induction j with
  | zero => simp [C, CliffordAlgebra.contractLeft_one]
  | succ j ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply]
    have ht : Matrix.vecTail (exteriorCoordinateProjection d a ∘ v) =
        exteriorCoordinateProjection d a ∘ Matrix.vecTail v := rfl
    rw [ht, ih (Matrix.vecTail v)]
    exact exteriorCoordinateProjection_mul d a (v 0) _

/-- 正次数の外冪に誘導された座標射影は、左外積と内部積の合成の補射影。 -/
theorem exteriorPower_map_coordinateProjection
    (d : Module.Dual k M) (a : M) (j : ℕ) :
    exteriorPower.map (j+1) (exteriorCoordinateProjection d a) =
      LinearMap.id - (wedgeOne k M j ((exteriorPower.oneEquiv k M).symm a)).comp
        (exteriorContract k M d j) := by
  apply exteriorPower.alternatingMapLinearEquiv.symm.injective
  ext v : 1
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply]
  apply Subtype.ext
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Submodule.coe_sub, wedgeOne_coe, exteriorContract_coe,
    exteriorPower.oneEquiv_symm_apply]
  rw [show ExteriorAlgebra.ιMulti k 1 (fun _ => a) = ExteriorAlgebra.ι k a by
    simp [ExteriorAlgebra.ιMulti_apply]]
  exact exteriorCoordinateProjection_ιMulti d a v

/-- 零次外冪では座標射影は恒等。 -/
theorem exteriorPower_map_coordinateProjection_zero (d : Module.Dual k M) (a : M) :
    exteriorPower.map 0 (exteriorCoordinateProjection d a) = LinearMap.id := by
  apply exteriorPower.alternatingMapLinearEquiv.symm.injective
  ext v : 1
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply]
  apply Subtype.ext
  simp

end SerrePositivity.DeRham
