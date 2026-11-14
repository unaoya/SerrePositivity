module

public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionSingleHom
public import SerrePositivity.EInfinity.PowerOperation.TateCoefficientClass

/-!
# 指定完全周期 Hom の離散係数のホモロジーと係数類

DAG XIII Construction 2.2.6 の係数側の補助。
同じ左正則周期解像度の Hom の零微分と指定評価同値から、ホモロジーを計算する。
Hom 側の零次数と、係数周期模型の負一次の指定類を比較する。
native spectral Tate・双加群への比較は、この鎖レベルの比較とは別に必要である。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex
variable (p : ℕ) [NeZero p] {k : Type u} [CommRing k] [CharP k p]
variable (A : Rep.{u} k (PowerOperationCyclicGroup.{u} p)) [A.IsTrivial]

/-- 同じ完全周期 Hom の、離散な自明係数での全次数のホモロジー。 -/
def cyclicResolutionSingleHomologyIso (i : ℤ) :
    (linearHomComplex k (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A)).homology i ≅
      ModuleCat.of k A :=
  let K := linearHomComplex k (powerOperationCompleteResolution p k)
    ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A)
  (K.isoHomologyπ (i - 1) i (by simp) (cyclicResolutionSingleHom_d p A _ _)).symm ≪≫
    K.iCyclesIso i (i + 1) (by simp) (cyclicResolutionSingleHom_d p A _ _) ≪≫
      (cyclicResolutionSingleDegreeEquiv p A i).toModuleIso

/-- 指定の Hom 零次と、同じ係数周期模型の負一次との比較。 -/
def cyclicResolutionCoefficientClassIso :
    (linearHomComplex k (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj
        (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k))).homology 0 ≅
      (powerOperationTateCoefficientComplex p k).homology (-1) :=
  cyclicResolutionSingleHomologyIso p _ 0 ≪≫
    (powerOperationTateCoefficientHomologyIso p k (-1)).symm

/-- Hom 側で 1 に対応する同じ指定類は、係数周期模型の指定類へ送られる。 -/
lemma cyclicResolutionCoefficientClassIso_value :
    (cyclicResolutionCoefficientClassIso (k := k) p).hom
      ((cyclicResolutionSingleHomologyIso p
        (Rep.trivial k (PowerOperationCyclicGroup.{u} p) k) 0).inv (1 : k)) =
      powerOperationTateCoefficientClass p k := by
  simp [cyclicResolutionCoefficientClassIso, powerOperationTateCoefficientClass]

end SerrePositivity.EInfinity.PowerOperation
