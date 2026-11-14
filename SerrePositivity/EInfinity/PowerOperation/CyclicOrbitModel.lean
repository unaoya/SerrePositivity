module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorInput
public import Mathlib.Algebra.Homology.Bifunctor

/-!
# 同じ巡回群の実射影解像度による orbit の鎖模型

DAG XIII Construction 2.2.6 の Tate 境界の比較に用いる前段。
余不変の評価が g^{-1} を使うため、係数解像度の生成元を g^{-1} に固定する。
実際の projective resolution とその直和全複体を保持する。
この時点で native な homotopy orbit との同定は主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 同じ巡回群の逆生成元による実射影解像度。 -/
def cyclicOrbitProjectiveResolution :
    ProjectiveResolution (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) :=
  Rep.FiniteCyclicGroup.resolution k (powerOperationCyclicGenerator p)⁻¹ (by
    intro g
    simpa only [Subgroup.zpowers_inv] using powerOperationCyclicGenerator_generates p g)

/-- 同じ鎖解像度を負の余鎖次数へ零延長する。 -/
def cyclicOrbitResolution : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ :=
  (cyclicOrbitProjectiveResolution p k).complex.extend ComplexShape.embeddingDownNat

lemma cyclicOrbitResolution_isZero_positive (i : ℤ) (hi : 0 < i) :
    IsZero ((cyclicOrbitResolution p k).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  change -(n : ℤ) ≠ i
  omega

/-- 同じ orbit 解像度の上界は零。 -/
lemma cyclicOrbitResolution_isStrictlyLE : (cyclicOrbitResolution p k).IsStrictlyLE 0 := by
  rw [isStrictlyLE_iff]
  exact cyclicOrbitResolution_isZero_positive p k

/-- 同じ入力と同じ解像度のテンソル余不変の直和全複体の全関手。 -/
def cyclicOrbitTotalFunctor :
    CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (Rep.coinvariantsTensor k (PowerOperationCyclicGroup.{u} p)).map₂CochainComplex ⋙
    (evaluation _ _).obj (cyclicOrbitResolution p k)

end SerrePositivity.EInfinity.PowerOperation
