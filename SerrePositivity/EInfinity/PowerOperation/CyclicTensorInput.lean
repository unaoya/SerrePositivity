module

public import SerrePositivity.EInfinity.PowerOperation.TensorPowerRepresentation
public import SerrePositivity.EInfinity.PowerOperation.CyclicTateResolution
public import Mathlib.Data.ZMod.Basic

/-!
# 指定 p 巡回作用を持つ p 重テンソル

DAG XIII Construction 2.2.6 の巡回部分群を、加法群 Z/p の左平行移動として固定する。
p 入力は既存の Koszul 置換作用を使う。係数周期複体の生成元も同じ 1 に固定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (p : ℕ) [NeZero p]

/-- 宇宙を係数環とそろえた p 巡回群。 -/
abbrev PowerOperationCyclicGroup := ULift.{u} (Multiplicative (ZMod p))

/-- Z/p の元による p 個の入力の指定巡回置換。 -/
def powerOperationCyclicPermutation :
    PowerOperationCyclicGroup.{u} p →* Equiv.Perm (Fin p) where
  toFun g := (ZMod.finEquiv p).toEquiv.trans
    ((Equiv.addLeft g.down.toAdd).trans (ZMod.finEquiv p).toEquiv.symm)
  map_one' := by ext i; simp
  map_mul' g h := by ext i; simp

/-- 周期微分に用いる、同じ巡回群の指定生成元。 -/
def powerOperationCyclicGenerator : PowerOperationCyclicGroup.{u} p :=
  ULift.up (Multiplicative.ofAdd (1 : ZMod p))

lemma powerOperationCyclicGroup_card : Fintype.card (PowerOperationCyclicGroup.{u} p) = p := by
  simp [PowerOperationCyclicGroup, ZMod.card]

lemma powerOperationCyclicGenerator_generates (g : PowerOperationCyclicGroup.{u} p) :
    g ∈ Subgroup.zpowers (powerOperationCyclicGenerator p) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(g.down.toAdd.val : ℤ), ?_⟩
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  simp [powerOperationCyclicGenerator]

/-- 指定巡回群を持つ p 入力の、全複体に関する全関手。 -/
def powerOperationTensorInput (k : Type u) [CommRing k] :
    Complex k ⥤ CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ :=
  tensorPowerRepresentationFunctor p (powerOperationCyclicPermutation p)

/-- 同じ指定生成元による左正則係数複体は全次数で完全。 -/
lemma powerOperationCyclicResolution_exactAt (k : Type u) [CommRing k] (i : ℤ) :
    (cyclicTateComplex (Rep.leftRegular k (PowerOperationCyclicGroup.{u} p))
      (powerOperationCyclicGenerator p)).ExactAt i :=
  cyclicTateComplex_leftRegular_exactAt k _ (powerOperationCyclicGenerator_generates p) i

end SerrePositivity.EInfinity.PowerOperation
