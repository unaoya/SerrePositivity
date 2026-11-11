module
public import SerrePositivity.KST.SConstruction.SimplexHADegreeDefect

/-! # 元の HA 頂点列と生成元微分条件の次元移送
概要：同じ cube 次元の異なる和表示の間で、元の頂点列と生成元上の差の零性を移す。
方針：次元等号と元の列・添字の異種等号を消去する。
規約：元の両端点と実微分を保持。使われ方：内部端点の左右表示による次元帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

/-- 同じ元の頂点列を、元の cube 次元の等号に沿って移す。 -/
def simplexHAOrderDimensionCast {N n m : ℕ} (h : n = m)
    (v : Fin (n + 1) ↪o Fin (N + 1)) : Fin (m + 1) ↪o Fin (N + 1) := by
  cases h
  exact v

/-- 元の次元移送は、元の列そのものを異種等号で保持する。 -/
lemma simplexHAOrderDimensionCast_heq {N n m : ℕ} (h : n = m)
    (v : Fin (n + 1) ↪o Fin (N + 1)) : HEq (simplexHAOrderDimensionCast h v) v := by
  cases h
  rfl

/-- 元の次元移送は、元の同じ始点を保持する。 -/
lemma simplexHAOrderDimensionCast_first {N n m : ℕ} (h : n = m)
    (v : Fin (n + 1) ↪o Fin (N + 1)) : simplexHAOrderDimensionCast h v 0 = v 0 := by
  cases h
  rfl

/-- 元の次元移送は、元の同じ最右頂点を保持する。 -/
lemma simplexHAOrderDimensionCast_last {N n m : ℕ} (h : n = m)
    (v : Fin (n + 1) ↪o Fin (N + 1)) :
    simplexHAOrderDimensionCast h v (Fin.last m) = v (Fin.last n) := by
  cases h
  rfl

variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の次元・添字・頂点列の移送は、元の生成元上の微分合成の差の零性を保つ。 -/
lemma simplexHADegreeDefect_generator_zero_heq {N n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (hn : n = m) (i : SerreCubeGeneratorIndex n) (j : SerreCubeGeneratorIndex m) (hi : HEq i j)
    (v : Fin (n + 1) ↪o Fin (N + 1)) (w : Fin (m + 1) ↪o Fin (N + 1)) (hv : HEq v w)
    (b : Fin (N + 1)) (hb : v (Fin.last n) < b) (hb' : w (Fin.last m) < b)
    (k : ℤ) (hk : serreCubeGeneratorDegree n i = k) (hk' : serreCubeGeneratorDegree m j = k) :
    (simplexHADegreeDefect A s n v b hb k
      (eqToHom (congrArg (fun d => (serreCubeComplex A n).X d) hk)
        (serreCubeGenerator A n i)) = 0) ↔
      (simplexHADegreeDefect A s m w b hb' k
        (eqToHom (congrArg (fun d => (serreCubeComplex A m).X d) hk')
          (serreCubeGenerator A m j)) = 0) := by
  cases hn
  cases hi
  cases hv
  rfl

end SerrePositivity.KST.SConstruction
