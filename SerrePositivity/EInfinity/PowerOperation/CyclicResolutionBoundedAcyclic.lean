module

public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionHomComplex
public import SerrePositivity.EInfinity.PowerOperation.BoundedAcyclicHomComplex

/-!
# 同じ完全周期解像度への有界係数の非輪状比較の適用

DAG XIII Construction 2.2.6 の完全入力の係数模型に用いる補助。
解像度の各項の射影性を供給し、値域の上有界性を明示したまま適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable (p : ℕ) [NeZero p] {k : Type u} [CommRing k]

/-- 指定解像度からの Hom は、上有界な非輪状の作用付き係数を非輪状に送る。 -/
lemma cyclicResolutionHom_acyclic_boundedAbove
    (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (hM : M.Acyclic) :
    ((cyclicResolutionHomFunctor p k).obj M).Acyclic := by
  let P := powerOperationCompleteResolution p k
  have (i : ℤ) : Projective (P.X i) :=
    cyclicTateComplex_leftRegular_projective k (powerOperationCyclicGenerator p) i
  exact linearHomComplex_acyclic_boundedAbove k P M d hM

end SerrePositivity.EInfinity.PowerOperation
