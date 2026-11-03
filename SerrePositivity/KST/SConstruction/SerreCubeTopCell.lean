module
public import SerrePositivity.KST.SConstruction.SerreCubeComonoid
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-! # 元の Serre 鎖立方体の最高次元生成元
概要：元の単位生成元と元の辺の tensor から、全次元の最高次元生成元を構成する。
方針：元の複体を変更せず、その tensor 微分の Leibniz 則を同じ生成元で評価する。
規約：cochain 次数は −n、元の因子順を保つ。使われ方：native HA 方程式の符号比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の n 次元鎖立方体の、元の全辺の tensor である最高次元生成元。 -/
def serreCubeTopCell : (n : ℕ) → (serreCubeComplex A n).X (-(n : ℤ))
  | 0 => (cycleFromUnit (𝟙_ (Complex A)) (𝟙 _)).val
  | n + 1 => ιTensorObj (serreCubeComplex A n) (serreInterval A)
      (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (by omega)
        (serreCubeTopCell n ⊗ₜ[A] serreIntervalEdge A)

/-- 元の零次元の最高生成元は、元の単位複体の同じ標準生成元。 -/
lemma serreCubeTopCell_zero :
    serreCubeTopCell A 0 = (cycleFromUnit (𝟙_ (Complex A)) (𝟙 _)).val := rfl

/-- 元の最高生成元の一段は、元の直前の生成元と同じ辺の tensor。 -/
lemma serreCubeTopCell_succ (n : ℕ) :
    serreCubeTopCell A (n + 1) =
      ιTensorObj (serreCubeComplex A n) (serreInterval A)
        (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (by omega)
          (serreCubeTopCell A n ⊗ₜ[A] serreIntervalEdge A) := rfl

/-- 元の零次元の最高生成元は閉じている。 -/
lemma serreCubeTopCell_zero_d :
    (serreCubeComplex A 0).d 0 1 (serreCubeTopCell A 0) = 0 :=
  (cycleFromUnit (𝟙_ (Complex A)) (𝟙 _)).property

/-- 元の最高生成元の微分は、元の tensor 微分の符号と辺の端点差を持つ。 -/
lemma serreCubeTopCell_succ_d (n : ℕ) :
    (serreCubeComplex A (n + 1)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (serreCubeTopCell A (n + 1)) =
      ιTensorObj (serreCubeComplex A n) (serreInterval A)
          (-(n : ℤ) + 1) (-1) (-(n : ℤ)) (by omega)
          ((serreCubeComplex A n).d (-(n : ℤ)) (-(n : ℤ) + 1)
            (serreCubeTopCell A n) ⊗ₜ[A] serreIntervalEdge A) +
        (-(n : ℤ)).negOnePow •
          ιTensorObj (serreCubeComplex A n) (serreInterval A)
            (-(n : ℤ)) 0 (-(n : ℤ)) (by omega)
              (serreCubeTopCell A n ⊗ₜ[A]
                ((cycleFromUnit _ (serreIntervalOne A)).val -
                  (cycleFromUnit _ (serreIntervalZero A)).val)) := by
  have hd (P Q : Complex A) (i j k l : ℤ) (hk : i + j = k) (hl : k + 1 = l)
      (x : P.X i) (y : Q.X j) :
      (P ⊗ Q).d k l (ιTensorObj P Q i j k hk (x ⊗ₜ[A] y)) =
        ιTensorObj P Q (i + 1) j l (by omega) (P.d i (i + 1) x ⊗ₜ[A] y) +
          i.negOnePow • ιTensorObj P Q i (j + 1) l (by omega)
            (x ⊗ₜ[A] Q.d j (j + 1) y) := by
    subst l
    exact SerrePositivity.DifferentialGraded.tensor_d_apply P Q i j k hk x y
  have h := hd (serreCubeComplex A n) (serreInterval A)
    (-(n : ℤ)) (-1) (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) (by omega)
    (serreCubeTopCell A n) (serreIntervalEdge A)
  exact h.trans (congrArg (fun z =>
    ιTensorObj (serreCubeComplex A n) (serreInterval A)
      (-(n : ℤ) + 1) (-1) (-(n : ℤ)) (by omega)
      ((serreCubeComplex A n).d (-(n : ℤ)) (-(n : ℤ) + 1)
        (serreCubeTopCell A n) ⊗ₜ[A] serreIntervalEdge A) +
      (-(n : ℤ)).negOnePow •
        ιTensorObj (serreCubeComplex A n) (serreInterval A)
          (-(n : ℤ)) 0 (-(n : ℤ)) (by omega) (serreCubeTopCell A n ⊗ₜ[A] z))
    (serreIntervalEdge_d A))

end SerrePositivity.KST.SConstruction
