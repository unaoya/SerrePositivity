module

public import SerrePositivity.EInfinity.PowerOperation.CyclicPeriodicRestriction
public import SerrePositivity.EInfinity.PowerOperation.RegularOrbitCoordinates

/-!
# 上有界係数の正の周期 Hom の有限座標

DAG XIII Construction 2.2.6 の orbit 境界比較の補助。
同じ切り詰めの項の同型と、同じ左正則評価で各次数を有限な積へ移す。
上界は係数ごとに指定し、非有界な積を直和と取り違えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]
variable (M : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ)
    (d : ℤ) [M.IsStrictlyLE d] (n : ℤ)

/-- 同じ正の周期 Hom の有限座標。 -/
def cyclicPositiveFiniteCoordinates :
    Cochain (cyclicPositiveResolution p k) M n ≃ₗ[k]
      ∀ i : {i : ℤ // i ∈ Finset.Icc 0 (d - n)}, M.X (i.1 + n) where
  toFun z i := Rep.leftRegularHomEquiv (M.X (i.1 + n))
    ((StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i.1
      (Finset.mem_Icc.mp i.2).1).inv ≫ z.v i.1 (i.1 + n) rfl)
  invFun x := Cochain.mk fun i j hij =>
    if hi : i ∈ Finset.Icc 0 (d - n) then
      (StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i
        (Finset.mem_Icc.mp hi).1).hom ≫
      (Rep.leftRegularHomEquiv (M.X (i + n))).symm (x ⟨i, hi⟩) ≫
      eqToHom (congrArg M.X hij)
    else 0
  map_add' z w := by
    funext i
    simp only [Cochain.add_v, Preadditive.comp_add, map_add, Pi.add_apply]
  map_smul' r z := by
    funext i
    simp only [Cochain.smul_v, Linear.comp_smul, map_smul, Pi.smul_apply,
      RingHom.id_apply]
  left_inv z := by
    apply Cochain.ext
    intro i j hij
    subst j
    by_cases hi : i ∈ Finset.Icc 0 (d - n)
    · simp only [Cochain.mk_v, dite_eq_left hi, eqToHom_refl, Category.comp_id,
        LinearEquiv.symm_apply_apply, Iso.hom_inv_id_assoc]
    · simp only [Cochain.mk_v, dite_eq_right hi]
      exact (cyclicPositiveResolutionHom_finiteSupport p k M d n z i (i + n) rfl hi).symm
  right_inv x := by
    funext i
    simp only [Cochain.mk_v, dite_eq_left i.2, eqToHom_refl, Category.comp_id,
      Iso.inv_hom_id_assoc, LinearEquiv.apply_symm_apply]

/-- 有限座標の同じ指定評価は、共通の上界を持つ全係数射に自然。 -/
lemma cyclicPositiveFiniteCoordinates_natural
    {N : CochainComplex (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) ℤ}
    [N.IsStrictlyLE d] (f : M ⟶ N)
    (z : Cochain (cyclicPositiveResolution p k) M n)
    (i : {i : ℤ // i ∈ Finset.Icc 0 (d - n)}) :
    cyclicPositiveFiniteCoordinates p k N d n
      (z.comp (Cochain.ofHom f) (add_zero n)) i =
    (f.f (i.1 + n)).hom (cyclicPositiveFiniteCoordinates p k M d n z i) := by
  change Rep.leftRegularHomEquiv _ (_ ≫
    (z.comp (Cochain.ofHom f) (add_zero n)).v i.1 (i.1 + n) rfl) =
    (f.f (i.1 + n)).hom (Rep.leftRegularHomEquiv _
      ((StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i.1
        (Finset.mem_Icc.mp i.2).1).inv ≫ z.v i.1 (i.1 + n) rfl))
  rw [Cochain.comp_zero_cochain_v]
  simpa only [Cochain.ofHom_v, ← Category.assoc] using
    regularHomEvaluation_natural (f.f (i.1 + n))
      ((StupidTruncation.aboveXIso (powerOperationCompleteResolution p k) 0 i.1
        (Finset.mem_Icc.mp i.2).1).inv ≫ z.v i.1 (i.1 + n) rfl)

end SerrePositivity.EInfinity.PowerOperation
