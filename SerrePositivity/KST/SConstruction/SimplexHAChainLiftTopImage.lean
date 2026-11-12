module
public import SerrePositivity.KST.SConstruction.SimplexHAChainLift

/-! # 元の実 HA Hom 鎖射の最高生成元による成分回収
概要：無条件に構成した実 Hom 鎖射の HA 向き最高生成元像は、元の同じ部分集合成分。
方針：全次数の線形復元の最高生成元値と元の向き符号の二乗一を使う。
規約：元の部分集合・端点・次数を保持。使われ方：native HA からの逆構成の右逆。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma map_units_smul (M P : ModuleCat.{u} A) (f : M ⟶ P) (e : ℤˣ) (x : M) :
    f (e • x) = e • f x := by
  simp only [Units.smul_def, map_zsmul]

/-- 元の実 Hom 鎖射の HA 向き最高生成元像は、同じ元の部分集合 HA 成分。 -/
lemma simplexHAChainLift_top_image {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1)) (hb : v (Fin.last m) < b) :
    serreCubeTopCellImage A (homObject A D (s.obj (v 0)) (s.obj b)) m
      (simplexHAChainLift A s m v b hb) =
      s.hom (simplexHADecodeSubset m v {b}) (v 0) b (-(m : ℤ))
        (simplexHADecodeSubset_two m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb))
        (simplexHADecodeSubset_min m v {b}
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm
        (simplexHADecodeSubset_max m v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)).symm (by
            have hc := simplexHADecodeSubset_card m v {b}
              (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)
            simp only [Finset.card_singleton] at hc
            omega) := by
  have h₀ := map_units_smul A _ _ ((simplexHAChainLift A s m v b hb).f (-(m : ℤ)))
    (serreCubeOrientationSign m) (serreCubeTopCell A m)
  have h₁ := congrArg (fun x => serreCubeOrientationSign m • x)
    (simplexHADegreeLift_top A s.toSimplexData m v b hb)
  exact h₀.trans (h₁.trans (by rw [smul_smul, Int.units_mul_self, one_smul]))

end SerrePositivity.KST.SConstruction
