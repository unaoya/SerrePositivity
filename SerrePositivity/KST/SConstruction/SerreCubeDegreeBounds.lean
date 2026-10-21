module
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorFaces
public import SerrePositivity.KST.SConstruction.SerreCubeGeneratorExt
public import SerrePositivity.KST.SConstruction.SerreCubeTopCellImage

/-! # 元の Serre 鎖立方体の下限次数と最高生成元像の消滅
概要：元の n 次元鎖立方体は −n より低い次数で零で、低次元因子を通る最高像は零。
方針：全 tensor 生成元の自由座標数と次数、元の次数線形射の判定を使う。
規約：元の実鎖複体と全生成元を保持。使われ方：退化した高次 HA 成分の実零性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded

/-- 元の tensor 生成元の自由座標数は、元の鎖立方体の次元を超えない。 -/
lemma serreCubeGeneratorFreeDimension_le (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    serreCubeGeneratorFreeDimension n i ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    obtain ⟨i, j⟩ := i
    have h := ih i
    fin_cases j <;> simp only [serreCubeGeneratorFreeDimension] <;> omega

/-- 元の全 tensor 生成元の cochain 次数は、元の次元の負値以上。 -/
lemma serreCubeGeneratorDegree_lower_bound (n : ℕ) (i : SerreCubeGeneratorIndex n) :
    -(n : ℤ) ≤ serreCubeGeneratorDegree n i := by
  rw [serreCubeGeneratorDegree_freeDimension]
  have h := serreCubeGeneratorFreeDimension_le n i
  omega

variable (A : Type u) [CommRing A]

/-- 元の鎖立方体の次元の負値より低い次数の加群は、実際に零対象。 -/
lemma serreCubeComplex_X_isZero_below (n : ℕ) (k : ℤ) (hk : k < -(n : ℤ)) :
    IsZero ((serreCubeComplex A n).X k) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply serreCube_degree_hom_ext A n k
  intro i hi
  have h := serreCubeGeneratorDegree_lower_bound n i
  omega

/-- 元の低次元 cube を通る実鎖射は、元の高次元の HA 向き最高生成元を零へ送る。 -/
lemma serreCubeTopCellImage_lower_dimension {n m : ℕ} (hm : m < n) {K : Complex A}
    (f : serreCubeComplex A n ⟶ serreCubeComplex A m) (g : serreCubeComplex A m ⟶ K) :
    serreCubeTopCellImage A K n (f ≫ g) = 0 := by
  have hs := ModuleCat.subsingleton_of_isZero
    (serreCubeComplex_X_isZero_below A m (-(n : ℤ)) (by omega))
  have hx : f.f (-(n : ℤ)) (serreCubeOrientedTopCell A n) = 0 := hs.elim _ _
  exact (congrArg (fun x => g.f (-(n : ℤ)) x) hx).trans (map_zero _)

end SerrePositivity.KST.SConstruction
