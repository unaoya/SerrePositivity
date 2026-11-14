module

public import SerrePositivity.EInfinity.PowerOperation.LinearHomConeComparison
public import SerrePositivity.EInfinity.PowerOperation.BoundedQuasiIsoCone
public import SerrePositivity.EInfinity.PowerOperation.BoundedAcyclicHomComplex
public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionHomComplex

/-!
# 有界係数の準同型を保つ完全周期 Hom

DAG XIII Construction 2.2.6 の完全入力の係数模型比較に用いる補助。
同じ指定射の cone を通して証明する。値域の上有界性は仮定に残し、
無限周期解像度の無条件の K 射影性へ読み替えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex

/-- 射影的な各項からの全 Hom は、上有界係数の指定準同型を保つ。 -/
lemma linearHomComplexPostcompose_quasiIso_boundedAbove
    (R : Type w) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
    (P : CochainComplex C ℤ) [∀ i, Projective (P.X i)]
    {M N : CochainComplex C ℤ} (f : M ⟶ N) [QuasiIso f]
    (d : ℤ) [M.IsStrictlyLE d] [N.IsStrictlyLE d] :
    QuasiIso (linearHomComplexPostcompose R P f) := by
  have : (mappingCone f).IsStrictlyLE d := coefficientCone_isStrictlyLE f d
  have hc := linearHomComplex_acyclic_boundedAbove R P (mappingCone f) d
    (coefficientCone_acyclic_of_quasiIso f)
  apply coefficientCone_quasiIso_of_acyclic
  intro i
  exact (hc i).of_iso (linearHomConeIso R P f).symm

/-- 同じ指定完全周期 Hom は、上有界な作用付き係数の準同型を保つ。 -/
lemma cyclicResolutionHom_quasiIso_boundedAbove (p : ℕ) [NeZero p]
    {k : Type u} [CommRing k]
    {M N : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ}
    (f : M ⟶ N) [QuasiIso f] (d : ℤ) [M.IsStrictlyLE d] [N.IsStrictlyLE d] :
    QuasiIso ((cyclicResolutionHomFunctor p k).map f) := by
  let P := powerOperationCompleteResolution p k
  have (i : ℤ) : Projective (P.X i) :=
    cyclicTateComplex_leftRegular_projective k (powerOperationCyclicGenerator p) i
  exact linearHomComplexPostcompose_quasiIso_boundedAbove k P f d

end SerrePositivity.EInfinity.PowerOperation
