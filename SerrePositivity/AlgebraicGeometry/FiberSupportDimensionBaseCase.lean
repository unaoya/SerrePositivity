module

public import SerrePositivity.AlgebraicGeometry.FiberSupportAnnihilator
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
概要：全ファイバーの台が空なら有限加群は零。
方針：元の台の各点を、その縮約点のファイバーの台へ持ち上げる。
規約：空の台の次元は `⊥` で表す。
使われ方：Stacks 0815 のファイバーの台の次元による帰納の初項。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：基底の各点でファイバーの台の次元が `⊥` なら、元の有限加群は零。
方針：有限加群の台とファイバーへの引き戻しが両立することを使う。
規約：加群の零性は `Subsingleton` で表す。
使われ方：空の台の場合はブローアップなしで純変換が平坦。
-/
theorem subsingleton_of_fiber_supportDim_eq_bot
    {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (h : ∀ p : PrimeSpectrum R, let C := p.asIdeal.Fiber B
      letI : Algebra B C := Algebra.TensorProduct.rightAlgebra
      Module.supportDim C (C ⊗[B] M) = ⊥) :
    Subsingleton M := by
  rw [← Module.support_eq_empty_iff (R := B) (M := M)]
  refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
  let p := q.comap (algebraMap R B)
  let C := p.asIdeal.Fiber B
  let : Algebra B C := Algebra.TensorProduct.rightAlgebra
  let e := PrimeSpectrum.preimageHomeomorphFiber R B p
  let x : PrimeSpectrum C := e ⟨q, rfl⟩
  have hx : x.comap (algebraMap B C) = q :=
    congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
  have hx' : x ∈ Module.support C (C ⊗[B] M) := by
    rw [support_tensorProduct_eq_preimage]
    change x.comap (algebraMap B C) ∈ Module.support B M
    rwa [hx]
  have hzero : Subsingleton (C ⊗[B] M) :=
    (Module.supportDim_eq_bot_iff_subsingleton C (C ⊗[B] M)).mp (h p)
  have hempty : Module.support C (C ⊗[B] M) = ∅ := Module.support_eq_empty_iff.mpr hzero
  exact (Set.eq_empty_iff_forall_notMem.mp hempty x) hx'


/--
概要：全ファイバーの台の次元が底なら、正則な境界を持つ全試験対象で純変換が平坦。
方針：元の加群が零なので、底変換と純変換の後も零。
規約：境界元と試験対象への射に追加条件は要らない。
使われ方：台の次元帰納の初項で恒等ブローアップを選ぶ。
-/
theorem hasFlatPurePullbacks_of_fiber_supportDim_eq_bot
    {R : CommRingCat.{u}} {X : Scheme.{u}} {B M : Type*}
    [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M] [Module B M] [Module.Finite B M]
    (p : X ⟶ Spec R) (a : R)
    (h : ∀ q : PrimeSpectrum R, let C := q.asIdeal.Fiber B
      letI : Algebra B C := Algebra.TensorProduct.rightAlgebra
      Module.supportDim C (C ⊗[B] M) = ⊥) :
    HasFlatPurePullbacks p a M := by
  let : Subsingleton M := subsingleton_of_fiber_supportDim_eq_bot h
  intro A j φ ha
  infer_instance

end SerrePositivity.AlgebraicGeometry
