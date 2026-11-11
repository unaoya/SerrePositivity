module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryTriangleCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryLift

/-! # 実 cone 境界からの二未知成分と微分式

概要：実 coslice 境界の残差を二つの Hom end の未知成分へ送る。
方針：二三角形残差の差を cone の原始元へ渡し、零側残差の符号倍を共通成分に取る。
規約：整合条件は実境界の Bianchi から証明済み。使われ方：β3 の実充填候補への挿入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

/-- cone 境界の座標の次数と Bianchi の符号の一致。 -/
lemma dgModuleConeBoundaryDegree_negOnePow (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow = ((n : ℤ) + 1).negOnePow := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n = -((n : ℤ) + 1) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree]
    omega
  rw [h, Int.negOnePow_neg]

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} {n : ℕ}
variable (f : M ⟶ N)
variable (b : (SSet.boundary (n + 1) : SSet) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f)))
variable (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f))

/-- cone 頂点側の未知成分を実境界の二三角形残差の差から作る。 -/
def dgModuleConeBoundaryLiftQ :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLift A D (X := ForgetEnrichment.of (Complex A)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget A D f b)) f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb)

/-- 始点側の共通未知成分を零側の三角形残差の符号倍に取る。 -/
def dgModuleConeBoundaryLiftA :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb

/-- 実境界から作った cone 側成分の微分は後続の残差そのもの。 -/
lemma dgModuleConeBoundaryLiftQ_differential :
    _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (dgModuleConeBoundaryLiftQ A D f b hb) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLift_differential A D f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n)
  · change _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow •
        (compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb) (moduleConeInlElement A D f)
          (show (-1) + (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 + 1) =
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 by omega) -
          (show _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget A D f b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1) from
            (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) f (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget A D f b))).f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1)
                (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb)))
    have hd : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) =
      differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb) -
        differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) := map_sub _ _ _
    rw [hd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB_differential,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC_differential_zero, dgModuleConeBoundaryDegree_negOnePow]
    have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHom_precompose_eq_compose A D
      (X := ForgetEnrichment.of (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryTarget A D f b)) f
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb)
    rw [hp]
    simp only [smul_add, smul_sub]
    abel
  · change differential (D := RightModule A D) A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow •
        compose A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhs0 A D f b hb)
          (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.moduleConeInr A D f))).val
          (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1 + 1))
    rw [dgModuleConeBoundaryDegree_negOnePow]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB_differential A D f b hb

/-- 実境界から作った共通始点成分の微分は始点側の残差。 -/
lemma dgModuleConeBoundaryLiftA_differential :
    _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A (dgModuleConeBoundaryLiftA A D f b hb) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsA A D f b hb := by
  have hsmul : _root_.SerrePositivity.DifferentialGraded.differential (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) A
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow •
        differential A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) := by
    simp only [_root_.SerrePositivity.DifferentialGraded.differential, Units.smul_def, map_zsmul]
  rw [dgModuleConeBoundaryLiftA, hsmul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC_differential_zero,
    dgModuleConeBoundaryDegree_negOnePow, smul_smul, Int.units_mul_self, one_smul]

/-- cone 側未知成分の左包含座標は二三角形残差の差の符号倍。 -/
lemma dgModuleConeBoundaryLiftQ_inl :
    _root_.SerrePositivity.DifferentialGraded.compose A (dgModuleConeBoundaryLiftQ A D f b hb) (_root_.SerrePositivity.DifferentialGraded.moduleConeInlElement A D f)
      (show (-1) + (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n by omega) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow •
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAB A D f b hb - _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsAC A D f b hb) :=
  congrArg Prod.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLift_coordinates A D f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n) _ _)

/-- cone 側未知成分の右包含座標は N 側残差の符号倍。 -/
lemma dgModuleConeBoundaryLiftQ_inr :
    _root_.SerrePositivity.DifferentialGraded.compose A (dgModuleConeBoundaryLiftQ A D f b hb) (_root_.SerrePositivity.DifferentialGraded.moduleConeInrElement A D f)
      (zero_add (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n).negOnePow • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryRhsB A D f b hb :=
  congrArg Prod.snd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryLift_coordinates A D f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryDegree n) _ _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
