module

public import SerrePositivity.EInfinity.PowerOperation.TensorPowerHomotopy

/-!
# 同じ符号付き置換作用を持つ p 入力の準同型保存

DAG XIII Construction 2.2.6 の完全入力の相対模型に用いる補助。
作用の同変性は既存の指定入力関手に含め、準同型性は正確な忘却で反映する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable {k G : Type u} [CommRing k] [Group G] {K L : Complex k}

/-- 同じ置換作用を持つ指定テンソル射は、K 射影的な入力の準同型を保つ。 -/
lemma tensorPowerRepresentationFunctor_map_quasiIso [K.IsKProjective] [L.IsKProjective]
    (f : K ⟶ L) [QuasiIso f] (n : ℕ) (σ : G →* Equiv.Perm (Fin n)) :
    QuasiIso ((tensorPowerRepresentationFunctor n σ).map f) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((tensorPowerRepresentationFunctor n σ).map f)
    (forget₂ (Rep.{u} k G) (ModuleCat k))).mp
  change QuasiIso (TensorPowers.map f n)
  exact tensorPowerMap_quasiIso_of_KProjective f n

end SerrePositivity.EInfinity.PowerOperation
