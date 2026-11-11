module

public import SerrePositivity.AlgebraicGeometry.FiberSupportDimensionBaseCase
public import SerrePositivity.AlgebraicGeometry.FreeOpenDimensionInduction
public import SerrePositivity.AlgebraicGeometry.IdealFlattening

/-!
概要：ファイバー台の次元による平坦化の帰納の初項。
方針：上限零のとき各ファイバーで台が空であることを使い、単位イデアルを中心に選ぶ。
規約：台の次元に一を足した値を帰納の上限にする。
使われ方：Stacks 0815 の台の次元帰納。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry
open scoped TensorProduct

private theorem eq_bot_of_add_one_le_zero {d : WithBot ℕ∞} (h : d + 1 ≤ 0) : d = ⊥ := by
  by_contra hd
  lift d to ℕ∞ using hd
  change (↑(d + 1) : WithBot ℕ∞) ≤ ↑(0 : ℕ∞) at h
  have he := WithBot.coe_le_coe.mp h
  have h₁ : (1 : ℕ∞) ≤ d + 1 := by
    simpa only [zero_add] using add_le_add (zero_le : (0 : ℕ∞) ≤ d) (le_refl (1 : ℕ∞))
  exact (not_le_of_gt (zero_lt_one' ℕ∞)) (h₁.trans he)

set_option backward.isDefEq.respectTransparency false in
/--
概要：台の次元に一を足した値の上限が零なら、許容なアフィン平坦化中心が存在する。
方針：台が空でないと仮定し、その点の剰余体ファイバーで台が空であることに反する。
規約：余核の次元降下と同じ右側剰余体ファイバーを使う。
使われ方：自然数の帰納を始める。
-/
theorem hasAffineFlatPureCentersBelow_zero : HasAffineFlatPureCentersBelow.{u} 0 := by
  intro R _ B M _ _ _ _ _ _ _ _ a _ _ hdim
  have hM : Subsingleton M := by
    rw [← Module.support_eq_empty_iff (R := B) (M := M)]
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    let p := q.comap (algebraMap R B)
    let F := p.asIdeal.ResidueField
    let D := B ⊗[R] F
    let E := p.asIdeal.Fiber B
    let e := PrimeSpectrum.preimageHomeomorphFiber R B p
    let z : PrimeSpectrum E := e ⟨q, rfl⟩
    let g := Algebra.TensorProduct.comm R B F
    let x : PrimeSpectrum D := z.comap g.toRingEquiv.toRingHom
    have hx : x.comap (algebraMap B D) = q :=
      congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
    have hx' : x ∈ Module.support D (D ⊗[B] M) := by
      rw [support_tensorProduct_eq_preimage]
      change x.comap (algebraMap B D) ∈ Module.support B M
      rwa [hx]
    have hzero : Subsingleton (D ⊗[B] M) :=
      (Module.supportDim_eq_bot_iff_subsingleton D (D ⊗[B] M)).mp
        (eq_bot_of_add_one_le_zero (hdim p))
    exact (Set.eq_empty_iff_forall_notMem.mp (Module.support_eq_empty_iff.mpr hzero) x) hx'
  refine ⟨⊤, IsNoetherian.noetherian _, basicOpen_le_affineCenterComplement_of_pow_mem
    (I := ⊤) (f := a) (n := 0) (by simp), ?_⟩
  intro C j φ hreg
  let : Subsingleton M := hM
  infer_instance

end SerrePositivity.AlgebraicGeometry
