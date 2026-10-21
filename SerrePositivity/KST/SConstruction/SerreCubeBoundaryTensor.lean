module
public import SerrePositivity.KST.SConstruction.SerreCubeTopFaces

/-! # 元の最高生成元の境界の一段の線形表示
概要：元の辺を右に付ける線形写像を使い、最高生成元の微分の再帰を次数移送なしで読む。
方針：元の tensor 微分を任意に指定した後続次数で評価する。
規約：同じ元の複体・生成元と符号。使われ方：全面境界和の帰納法。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の辺を右に tensor する、指定次数間の実線形写像。 -/
def serreCubeAppendEdge (n : ℕ) (p k : ℤ) (hk : p + (-1) = k) :
    (serreCubeComplex A n).X p →ₗ[A] (serreCubeComplex A (n + 1)).X k :=
  (ιTensorObj (serreCubeComplex A n) (serreInterval A) p (-1) k hk).hom.comp
    ((TensorProduct.mk A ((serreCubeComplex A n).X p) ((serreInterval A).X (-1))).flip
      (serreIntervalEdge A))

/-- 元の辺の付加の評価は、元の同じ tensor 成分への包含。 -/
lemma serreCubeAppendEdge_apply (n : ℕ) (p k : ℤ) (hk : p + (-1) = k)
    (x : (serreCubeComplex A n).X p) :
    serreCubeAppendEdge A n p k hk x =
      ιTensorObj (serreCubeComplex A n) (serreInterval A) p (-1) k hk
        (x ⊗ₜ[A] serreIntervalEdge A) := rfl

/-- 元の tensor 微分の Leibniz 則を、全ての指定した後続次数で評価する。 -/
lemma serreTensorDifferential_apply (P Q : Complex A)
    (i i' j j' k k' : ℤ) (hi : i + 1 = i') (hj : j + 1 = j')
    (hk : i + j = k) (hk' : k + 1 = k') (x : P.X i) (y : Q.X j) :
    (P ⊗ Q).d k k' (ιTensorObj P Q i j k hk (x ⊗ₜ[A] y)) =
      ιTensorObj P Q i' j k' (by omega) (P.d i i' x ⊗ₜ[A] y) +
        i.negOnePow • ιTensorObj P Q i j' k' (by omega) (x ⊗ₜ[A] Q.d j j' y) := by
  subst i'
  subst j'
  subst k'
  exact SerrePositivity.DifferentialGraded.tensor_d_apply P Q i j k hk x y

/-- 元の最高生成元の微分の一段は、直前の微分への辺付加と右端二面の差。 -/
lemma serreCubeTopCell_succ_succ_d (n : ℕ) :
    (serreCubeComplex A (n + 2)).d (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ))
        (serreCubeTopCell A (n + 2)) =
      serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
          ((serreCubeComplex A (n + 1)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
            (serreCubeTopCell A (n + 1))) +
        (-((n + 1 : ℕ) : ℤ)).negOnePow •
          ((serreCubeFace A true (n + 1) 0).hom.f (-((n + 1 : ℕ) : ℤ))
              (serreCubeTopCell A (n + 1)) -
            (serreCubeFace A false (n + 1) 0).hom.f (-((n + 1 : ℕ) : ℤ))
              (serreCubeTopCell A (n + 1))) := by
  have h := serreTensorDifferential_apply A (serreCubeComplex A (n + 1)) (serreInterval A)
    (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (-1) 0
    (-((n + 2 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega) (by omega)
    (by omega) (by omega) (serreCubeTopCell A (n + 1)) (serreIntervalEdge A)
  exact h.trans (congrArg (fun z =>
    serreCubeAppendEdge A (n + 1) (-(n : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega)
      ((serreCubeComplex A (n + 1)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (serreCubeTopCell A (n + 1))) + (-((n + 1 : ℕ) : ℤ)).negOnePow • z)
    ((congrArg (fun z =>
      ιTensorObj (serreCubeComplex A (n + 1)) (serreInterval A)
        (-((n + 1 : ℕ) : ℤ)) 0 (-((n + 1 : ℕ) : ℤ)) (by omega)
        (serreCubeTopCell A (n + 1) ⊗ₜ[A] z)) (serreIntervalEdge_d A)).trans
      (serreCubeTopCell_face_zero_difference A (n + 1)).symm))

end SerrePositivity.KST.SConstruction
