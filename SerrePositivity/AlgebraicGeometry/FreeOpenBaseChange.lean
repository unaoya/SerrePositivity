module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：自由化主開とファイバーとの交わりは、基底の主開への制限で保たれる。
方針：自由性は局所化とテンソル積の取消、交わりは剰余体の比較で示す。
規約：自由性の保存は任意の代数拡大、ファイバーでの非零性の保存は平坦な族を扱う。
使われ方：Stacks 0815 で自由化主開の像の中へ基底を縮める。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：主開で自由な加群は、係数を拡大した後もその主開の逆像で自由。
方針：二つの局所化を結ぶ係数写像を作り、どちらも同じ二段テンソル積にする。
規約：元の加群や係数拡大の平坦性を仮定しない。
使われ方：自由化主開が基底を覆うよう、基底を主開に縮める。
-/
theorem free_baseChange_away_of_free
    {B C N : Type*} [CommRing B] [CommRing C] [Algebra B C]
    [AddCommGroup N] [Module B N] (b : B)
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)] :
    let L := Localization.Away (algebraMap B C b)
    Module.Free L (L ⊗[C] (C ⊗[B] N)) := by
  let K := Localization.Away b
  let L := Localization.Away (algebraMap B C b)
  have hunit : IsUnit (algebraMap B L b) := by
    rw [IsScalarTower.algebraMap_apply B C L]
    exact IsLocalization.Away.algebraMap_isUnit _
  let j : K →+* L := IsLocalization.Away.lift b hunit
  let : Algebra K L := j.toAlgebra
  let : IsScalarTower B K L :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp b hunit).symm
  let eC := TensorProduct.AlgebraTensorModule.cancelBaseChange B C L L N
  let eK := TensorProduct.AlgebraTensorModule.cancelBaseChange B K L L N
  exact Module.Free.of_equiv (eK.trans eC.symm)

/--
概要：平坦な族で指定ファイバーにおける元の非零性は、その点の上の任意の底変換ファイバーでも保たれる。
方針：剰余体の単射を平坦性でテンソルし、二段の底変換を一段にする。
規約：ファイバーの剰余体はテンソル積の左因子とする。
使われ方：自由化主開が基底の主近傍の全ファイバーと交わることを、局所化環上で使う。
-/
theorem fiber_tmul_ne_zero_after_baseChange
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B] (q : PrimeSpectrum A) (b : B)
    (hb : ((1 : (q.comap (algebraMap R A)).asIdeal.ResidueField) ⊗ₜ[R] b) ≠ 0) :
    ((1 : q.asIdeal.ResidueField) ⊗ₜ[A]
      (1 ⊗ₜ[R] b : A ⊗[R] B)) ≠ 0 := by
  let p := q.comap (algebraMap R A)
  let k := p.asIdeal.ResidueField
  let K := q.asIdeal.ResidueField
  let i : k →ₐ[R] K := Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R A) rfl
  let j := i.toLinearMap.rTensor B
  have hj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap i.toLinearMap i.injective
  let e := Algebra.TensorProduct.cancelBaseChange R A K K B
  intro hz
  apply hb
  apply hj
  have h := congrArg e hz
  change j ((1 : k) ⊗ₜ[R] b) = j 0
  simpa [e, j, i] using h

end SerrePositivity.AlgebraicGeometry
