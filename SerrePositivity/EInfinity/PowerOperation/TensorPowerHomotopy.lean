module

public import SerrePositivity.EInfinity.PowerOperation.TensorPowerRepresentation
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# 同じ p 重テンソルの指定射の準同型性

DAG XIII Construction 2.2.6 の完全入力の模型比較に用いる補助。
K 射影的な入力間の準同型を、元の指定射を保つホモトピー同値で処理する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {k : Type u} [CommRing k] {K L : Complex k}

/-- 同じテンソル冪の指定ホモトピー同値。 -/
def tensorPowerHomotopyEquiv (e : HomotopyEquiv K L) :
    ∀ n, HomotopyEquiv (power K n) (power L n)
  | 0 => HomotopyEquiv.refl _
  | n + 1 => cochainTensorHomotopyEquiv e (tensorPowerHomotopyEquiv e n)

lemma tensorPowerHomotopyEquiv_hom (e : HomotopyEquiv K L) (n : ℕ) :
    (tensorPowerHomotopyEquiv e n).hom = TensorPowers.map e.hom n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply HomologicalComplex.Hom.ext
    funext i
    exact congrArg (fun g => (cochainTensorMap e.hom g).f i) ih

/-- K 射影的な二入力の同じ指定準同型の p 乗は準同型。 -/
lemma tensorPowerMap_quasiIso_of_KProjective [K.IsKProjective] [L.IsKProjective]
    (f : K ⟶ L) [QuasiIso f] (n : ℕ) : QuasiIso (TensorPowers.map f n) := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  have h : (tensorPowerHomotopyEquiv e n).hom = TensorPowers.map f n := by
    rw [tensorPowerHomotopyEquiv_hom, he]
  rw [← h]
  infer_instance

end SerrePositivity.EInfinity.PowerOperation
