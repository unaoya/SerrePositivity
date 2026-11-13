module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorInput
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# May の巡回部分群と生成元の規約

May, Definitions 1.2・2.1 の巡回解像度を、BE の実置換群の部分群で読む。
入力の標準生成元は (0,…,p−1) を (p−1,0,…,p−2) に送る右回転。
以前の Tate 経路の群・作用の公開定義は変更しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
variable (p : ℕ) [NeZero p]

/-- 同じ巡回置換を BE の宇宙を持ち上げた置換群へ送る。 -/
def mayCyclicPermutation :
    PowerOperationCyclicGroup.{u} p →* ULift.{u} (Equiv.Perm (Fin p)) where
  toFun g := ULift.up (powerOperationCyclicPermutation p g)
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

lemma mayCyclicPermutation_injective : Function.Injective (mayCyclicPermutation.{u} p) := by
  intro g h he
  have h' := congrArg (fun f => (ZMod.finEquiv p) (f.down ((ZMod.finEquiv p).symm 0))) he
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  simpa [mayCyclicPermutation, powerOperationCyclicPermutation] using h'

/-- BE の実際の対称群の巡回部分群。 -/
abbrev MayCyclicGroup := (mayCyclicPermutation.{u} p).range

/-- 既存の加法群 Z/p の模型と、実置換部分群の指定同型。 -/
def mayCyclicGroupEquiv : PowerOperationCyclicGroup.{u} p ≃* MayCyclicGroup.{u} p :=
  MonoidHom.ofInjective (mayCyclicPermutation_injective p)

instance mayCyclicGroupCommGroup : CommGroup (MayCyclicGroup.{u} p) :=
  MonoidHom.commGroupOfInjective (mayCyclicGroupEquiv p).symm.toMonoidHom
    (mayCyclicGroupEquiv p).symm.injective

lemma mayCyclicGroup_card : Fintype.card (MayCyclicGroup.{u} p) = p := by
  rw [← Fintype.card_congr (mayCyclicGroupEquiv.{u} p).toEquiv]
  exact powerOperationCyclicGroup_card p

/-- May の右回転に一致する、実部分群の指定生成元。 -/
def mayCyclicGenerator : MayCyclicGroup.{u} p :=
  (mayCyclicGroupEquiv p (powerOperationCyclicGenerator p))⁻¹

lemma mayCyclicGenerator_generates (g : MayCyclicGroup.{u} p) :
    g ∈ Subgroup.zpowers (mayCyclicGenerator p) := by
  rw [mayCyclicGenerator, Subgroup.zpowers_inv]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
    (powerOperationCyclicGenerator_generates p ((mayCyclicGroupEquiv p).symm g))
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨n, ?_⟩
  calc
    mayCyclicGroupEquiv p (powerOperationCyclicGenerator p) ^ n =
        mayCyclicGroupEquiv p (powerOperationCyclicGenerator p ^ n) :=
      (map_zpow (mayCyclicGroupEquiv p) _ n).symm
    _ = g := by rw [hn, MulEquiv.apply_symm_apply]

/-- 指定生成元は入力の添字を一つ戻す。 -/
lemma mayCyclicGenerator_apply (i : Fin p) :
    (mayCyclicGenerator p).1.down i =
      (ZMod.finEquiv p).symm ((ZMod.finEquiv p) i - 1) := by
  change (powerOperationCyclicPermutation p (powerOperationCyclicGenerator p))⁻¹ i = _
  rw [← map_inv]
  simp [powerOperationCyclicPermutation, powerOperationCyclicGenerator, sub_eq_add_neg, add_comm]

end SerrePositivity.EInfinity.PowerOperation
