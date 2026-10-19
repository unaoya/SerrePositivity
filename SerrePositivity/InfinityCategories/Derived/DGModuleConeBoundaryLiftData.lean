module
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryTriangleCompatibility
public import SerrePositivity.InfinityCategories.Derived.DGModuleConeBoundaryLift

/-! # 実 cone 境界からの二未知成分と微分式

概要：実 coslice 境界の残差を二つの Hom end の未知成分へ送る。
方針：二三角形残差の差を cone の原始元へ渡し、零側残差の符号倍を共通成分に取る。
規約：整合条件は実境界の Bianchi から証明済み。使われ方：β3 の実充填候補への挿入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

/-- cone 境界の座標の次数と Bianchi の符号の一致。 -/
lemma dgModuleConeBoundaryDegree_negOnePow (n : ℕ) :
    (dgModuleConeBoundaryDegree n).negOnePow = ((n : ℤ) + 1).negOnePow := by
  have h : dgModuleConeBoundaryDegree n = -((n : ℤ) + 1) := by
    dsimp only [dgModuleConeBoundaryDegree]
    omega
  rw [h, Int.negOnePow_neg]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} {n : ℕ}
variable (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶ sliceUnder (pushoutSpan (dgModuleConeSquare A D f)))
variable (hb : boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (dgModuleConeCocone A D f))

/-- cone 頂点側の未知成分を実境界の二三角形残差の差から作る。 -/
def dgModuleConeBoundaryLiftQ :
    GradedHom A (ForgetEnrichment.to (Complex A) (moduleCone A D f))
      (dgModuleConeBoundaryTarget A D f b) (dgModuleConeBoundaryDegree n + 1) :=
  dgModuleConeBoundaryLift A D (X := ForgetEnrichment.of (Complex A)
    (dgModuleConeBoundaryTarget A D f b)) f (dgModuleConeBoundaryDegree n)
    (dgModuleConeBoundaryRhsAB A D f b hb - dgModuleConeBoundaryRhsAC A D f b hb)
    (dgModuleConeBoundaryRhsB A D f b hb)

/-- 始点側の共通未知成分を零側の三角形残差の符号倍に取る。 -/
def dgModuleConeBoundaryLiftA :
    GradedHom A (ForgetEnrichment.to (Complex A) M)
      (dgModuleConeBoundaryTarget A D f b) (dgModuleConeBoundaryDegree n) :=
  (dgModuleConeBoundaryDegree n).negOnePow • dgModuleConeBoundaryRhsAC A D f b hb

/-- 実境界から作った cone 側成分の微分は後続の残差そのもの。 -/
lemma dgModuleConeBoundaryLiftQ_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryLiftQ A D f b hb) =
      dgModuleConeBoundaryRhs0 A D f b hb := by
  apply dgModuleConeBoundaryLift_differential A D f (dgModuleConeBoundaryDegree n)
  · change differential (D := RightModule A D) A
        (dgModuleConeBoundaryRhsAB A D f b hb - dgModuleConeBoundaryRhsAC A D f b hb) =
      (dgModuleConeBoundaryDegree n).negOnePow •
        (compose A (dgModuleConeBoundaryRhs0 A D f b hb) (moduleConeInlElement A D f)
          (show (-1) + (dgModuleConeBoundaryDegree n + 1 + 1) =
            dgModuleConeBoundaryDegree n + 1 by omega) -
          (show GradedHom A (ForgetEnrichment.to (Complex A) M)
            (dgModuleConeBoundaryTarget A D f b) (dgModuleConeBoundaryDegree n + 1) from
            (eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A)
              (dgModuleConeBoundaryTarget A D f b))).f (dgModuleConeBoundaryDegree n + 1)
                (dgModuleConeBoundaryRhsB A D f b hb)))
    have hd : differential (D := RightModule A D) A
        (dgModuleConeBoundaryRhsAB A D f b hb - dgModuleConeBoundaryRhsAC A D f b hb) =
      differential A (dgModuleConeBoundaryRhsAB A D f b hb) -
        differential A (dgModuleConeBoundaryRhsAC A D f b hb) := map_sub _ _ _
    rw [hd, dgModuleConeBoundaryRhsAB_differential,
      dgModuleConeBoundaryRhsAC_differential_zero, dgModuleConeBoundaryDegree_negOnePow]
    have hp := dgModuleHom_precompose_eq_compose A D
      (X := ForgetEnrichment.of (Complex A) (dgModuleConeBoundaryTarget A D f b)) f
      (dgModuleConeBoundaryDegree n + 1) (dgModuleConeBoundaryRhsB A D f b hb)
    rw [hp]
    simp only [smul_add, smul_sub]
    abel
  · change differential (D := RightModule A D) A (dgModuleConeBoundaryRhsB A D f b hb) =
      (dgModuleConeBoundaryDegree n).negOnePow •
        compose A (dgModuleConeBoundaryRhs0 A D f b hb)
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (moduleConeInr A D f))).val
          (zero_add (dgModuleConeBoundaryDegree n + 1 + 1))
    rw [dgModuleConeBoundaryDegree_negOnePow]
    exact dgModuleConeBoundaryRhsB_differential A D f b hb

/-- 実境界から作った共通始点成分の微分は始点側の残差。 -/
lemma dgModuleConeBoundaryLiftA_differential :
    differential (D := RightModule A D) A (dgModuleConeBoundaryLiftA A D f b hb) =
      dgModuleConeBoundaryRhsA A D f b hb := by
  have hsmul : differential (D := RightModule A D) A
      ((dgModuleConeBoundaryDegree n).negOnePow • dgModuleConeBoundaryRhsAC A D f b hb) =
      (dgModuleConeBoundaryDegree n).negOnePow •
        differential A (dgModuleConeBoundaryRhsAC A D f b hb) := by
    simp only [differential, Units.smul_def, map_zsmul]
  rw [dgModuleConeBoundaryLiftA, hsmul, dgModuleConeBoundaryRhsAC_differential_zero,
    dgModuleConeBoundaryDegree_negOnePow, smul_smul, Int.units_mul_self, one_smul]

/-- cone 側未知成分の左包含座標は二三角形残差の差の符号倍。 -/
lemma dgModuleConeBoundaryLiftQ_inl :
    compose A (dgModuleConeBoundaryLiftQ A D f b hb) (moduleConeInlElement A D f)
      (show (-1) + (dgModuleConeBoundaryDegree n + 1) = dgModuleConeBoundaryDegree n by omega) =
      (dgModuleConeBoundaryDegree n).negOnePow •
        (dgModuleConeBoundaryRhsAB A D f b hb - dgModuleConeBoundaryRhsAC A D f b hb) :=
  congrArg Prod.fst (dgModuleConeBoundaryLift_coordinates A D f (dgModuleConeBoundaryDegree n) _ _)

/-- cone 側未知成分の右包含座標は N 側残差の符号倍。 -/
lemma dgModuleConeBoundaryLiftQ_inr :
    compose A (dgModuleConeBoundaryLiftQ A D f b hb) (moduleConeInrElement A D f)
      (zero_add (dgModuleConeBoundaryDegree n + 1)) =
      (dgModuleConeBoundaryDegree n).negOnePow • dgModuleConeBoundaryRhsB A D f b hb :=
  congrArg Prod.snd (dgModuleConeBoundaryLift_coordinates A D f (dgModuleConeBoundaryDegree n) _ _)

end SerrePositivity.InfinityCategories
