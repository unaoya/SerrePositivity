module
public import SerrePositivity.KST.SConstruction.SimplexHATopValueRecovery

/-! # 元の HA 線形復元の最高生成元像の微分
概要：任意の native HA 単体の最高生成元像の微分を、元の HA 右辺へ戻す。
方針：元の全辺値の回収と単体の HA 方程式を、元の向き符号を保って合成する。
規約：微分は +1、元の頂点集合と次数を指定。使われ方：実面像和との微分比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma differential_units_smul {x y : D} {k : ℤ}
    (e : ℤˣ) (f : GradedHom A x y k) :
    differential A (e • f) = e • differential A f := by
  change (homObject A D x y).d k (k + 1) (e • f) =
    e • (homObject A D x y).d k (k + 1) f
  simp only [Units.smul_def, map_zsmul]

/-- 元の HA 単体の最高生成元像の微分は、同じ向きの元の HA 右辺。 -/
lemma simplexHADegreeLift_top_differential {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D n)
    (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1)) (b : Fin (n + 1))
    (hvb : v (Fin.last m) < b) (I : Finset (Fin (n + 1)))
    (hIeq : I = simplexHADecodeSubset m v {b}) (hI : 2 ≤ I.card)
    (ha : v 0 = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : -(m : ℤ) = 2 - (I.card : ℤ)) :
    differential A
      (simplexHADegreeLift A s.toSimplexData m v b hvb (-(m : ℤ)) (serreCubeTopCell A m)) =
      serreCubeOrientationSign m • s.toSimplexData.rhs I (v 0) b (-(m : ℤ)) hI ha hb hk := by
  subst I
  exact (congrArg (differential A)
    (simplexHADegreeLift_top A s.toSimplexData m v b hvb)).trans
      ((differential_units_smul A (serreCubeOrientationSign m) _).trans
        (congrArg (fun w => serreCubeOrientationSign m • w)
          (s.equation _ _ _ _ hI ha hb hk)))

end SerrePositivity.KST.SConstruction
