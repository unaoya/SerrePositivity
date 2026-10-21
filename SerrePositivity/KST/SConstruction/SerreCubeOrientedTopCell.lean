module
public import SerrePositivity.KST.SConstruction.SerreCubeTopBoundary
public import SerrePositivity.KST.SConstruction.SerreCubeOrientationSigns

/-! # 元の Serre 最高生成元の HA 向きでの全面微分式
概要：元の最高生成元の向きだけを補正すると、微分は右側頂点数による零面−一面の和。
方針：元の全面境界式と向き補正の整数符号を、元の同じ生成元上で合成する。
規約：元の複体と面を変更しない。使われ方：native HA 方程式の削除・分割合成項。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped BigOperators
variable (A : Type u) [CommRing A]

/-- 元の最高生成元に三角数の符号を掛けた、同じ元の複体内の HA 向きの生成元。 -/
def serreCubeOrientedTopCell (n : ℕ) : (serreCubeComplex A n).X (-(n : ℤ)) :=
  serreCubeOrientationSign n • serreCubeTopCell A n

/-- 元の零次元では向き補正後も同じ単位生成元。 -/
lemma serreCubeOrientedTopCell_zero : serreCubeOrientedTopCell A 0 = serreCubeTopCell A 0 := by
  exact (congrArg (fun s => s • serreCubeTopCell A 0) serreCubeOrientationSign_zero).trans
    (one_smul _ _)

/-- 元の正次元の向き補正後の微分は、右側頂点数 i+1 の符号を持つ元の零面−一面の和。 -/
lemma serreCubeOrientedTopCell_d (n : ℕ) :
    (serreCubeComplex A (n + 1)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        (serreCubeOrientedTopCell A (n + 1)) =
      ∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
        ((serreCubeFace A false n i).hom.f (-(n : ℤ)) (serreCubeOrientedTopCell A n) -
          (serreCubeFace A true n i).hom.f (-(n : ℤ)) (serreCubeOrientedTopCell A n)) := by
  have hm (V W : ModuleCat.{u} A) (f : V ⟶ W) (s : ℤˣ) (x : V) :
      f (s • x) = s • f x := by
    simp only [Units.smul_def, map_zsmul]
  have ht (M : Type u) [AddCommGroup M] (s t : ℤˣ) (x y : M) :
      (-(s * t)) • (x - y) = s • (t • y - t • x) := by
    simp only [Units.smul_def, Units.val_neg, Units.val_mul, neg_smul, smul_sub, smul_smul]
    abel
  refine (hm _ _ ((serreCubeComplex A (n + 1)).d _ _)
    (serreCubeOrientationSign (n + 1)) (serreCubeTopCell A (n + 1))).trans ?_
  refine (congrArg (fun z => serreCubeOrientationSign (n + 1) • z)
    (serreCubeTopCell_d A n)).trans ?_
  change serreCubeOrientationSign (n + 1) •
    (∑ i : Fin (n + 1), ((n : ℤ) - (i.val : ℤ)).negOnePow •
      serreCubeTopFaceDifference A n i) = _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (smul_smul _ _ _).trans
    ((congrArg (fun s => s • serreCubeTopFaceDifference A n i)
      (serreCubeOrientationSign_boundary n (i.val : ℤ))).trans
      ((ht _ ((i.val : ℤ) + 1).negOnePow (serreCubeOrientationSign n)
        ((serreCubeFace A true n i).hom.f (-(n : ℤ)) (serreCubeTopCell A n))
        ((serreCubeFace A false n i).hom.f (-(n : ℤ)) (serreCubeTopCell A n))).trans
        (congrArg₂ (fun x y => ((i.val : ℤ) + 1).negOnePow • (x - y))
          (hm _ _ ((serreCubeFace A false n i).hom.f (-(n : ℤ)))
            (serreCubeOrientationSign n) (serreCubeTopCell A n)).symm
          (hm _ _ ((serreCubeFace A true n i).hom.f (-(n : ℤ)))
            (serreCubeOrientationSign n) (serreCubeTopCell A n)).symm)))

end SerrePositivity.KST.SConstruction
