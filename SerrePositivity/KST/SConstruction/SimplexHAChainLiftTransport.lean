module
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftRecovery
public import SerrePositivity.KST.SConstruction.SimplexHAOrderDimensionCast

/-! # 元の HA 実鎖射の次元・頂点列・終点の移送
概要：同じ元の列と終点の異なる表示で、元の HA 実鎖射を回収する。
方針：元の次元と頂点列の等号を消去する。
規約：元の実鎖射と全次数を保持。使われ方：全区間と左右切断の合成保存。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 同じ次元・頂点列・終点を保つ表示変更は、元の HA 実鎖射を異種等号で保つ。 -/
lemma simplexHAChainLift_heq {N n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (h : n = m) (v : Fin (n + 1) ↪o Fin (N + 1)) (w : Fin (m + 1) ↪o Fin (N + 1))
    (hv : HEq v w) (b c : Fin (N + 1)) (hbc : b = c)
    (hb : v (Fin.last n) < b) (hc : w (Fin.last m) < c) :
    HEq (simplexHAChainLift A s n v b hb) (simplexHAChainLift A s m w c hc) := by
  cases h
  cases hv
  cases hbc
  rfl

/-- 元の列の次元移送は、同じ cube の前合成と始点表示の後移送を回収する。 -/
lemma simplexHAChainLift_dimension {N n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (h : n = m) (v : Fin (n + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last n) < b)
    (hc : simplexHAOrderDimensionCast h v (Fin.last m) < b) :
    simplexHAChainLift A s m (simplexHAOrderDimensionCast h v) b hc ≫
        eqToHom (congrArg (fun x => homObject A D (s.obj x) (s.obj b))
          (simplexHAOrderDimensionCast_first h v)) =
      eqToHom (congrArg (serreCubeComplex A) h.symm) ≫ simplexHAChainLift A s n v b hb := by
  cases h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end SerrePositivity.KST.SConstruction
